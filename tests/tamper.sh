#!/bin/bash
# Tampering tests for gate.sh (adapted from earlier projects).
# Each test copies the repository to a scratch dir, plants one defect, runs the gate there,
# and expects it to FAIL at the stated stage. The real repository is never modified.
# Tests run one at a time (Lean builds are memory-heavy).
# Defects are planted in NagelLine/Basic.lean (falsehyp: in NagelLine/Main.lean).
# Usage: bash tests/tamper.sh [tests...]   (default: sorry ax2line evalfake macro wrap falsehyp falsehyp_ext)
# falsehyp drops the only hypothesis `(t : Triangle ℝ P)` (the non-degenerate triangle) from the
# main theorem `nagelPoint_vsub_centroid`, so the statement/proof no longer elaborates and the gate
# must fail at the build stage.
# falsehyp_ext does the same for the extension theorem `spiekerCenter_power_exsphere`
# (NagelLine/Extensions.lean).
set -u
export PATH="$HOME/.elan/bin:$PATH"
SRC="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/nagelline_tamper_XXXXXX")"
C=NagelLine/Basic.lean
H=NagelLine/Main.lean
X=NagelLine/Extensions.lean
EL='end NagelLine'

ins_before_last() { _T="$2" _M="$3" awk '{ L[NR]=$0; if ($0==ENVIRON["_M"]) last=NR } END { if (!last) exit 1; for(i=1;i<=NR;i++){ if(i==last) printf "%s\n", ENVIRON["_T"]; print L[i] } }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
subst_lit()      { _O="$2" _N="$3" _A="${4-}" awk '{ A=ENVIRON["_A"]; O=ENVIRON["_O"]; if(!done){ off=0; if(A!="" && !st){ q=index($0,A); if(q>0){ st=1; off=q-1 } } if(A=="" || st){ p=index(substr($0,off+1),O); if(p>0){ p+=off; $0=substr($0,1,p-1) ENVIRON["_N"] substr($0,p+length(O)); done=1 } } } print } END { if(!done) exit 1 }' "$1" > "$1.$$.tmp" && mv "$1.$$.tmp" "$1" || { rm -f "$1.$$.tmp"; return 1; }; }
[ -e "$SRC/.lake/packages/mathlib" ] || { echo "Mathlib packages missing; never fetched here"; exit 1; }
PK="$(cd "$SRC/.lake/packages" && pwd -P)"

mk() {
  mkdir -p "$WORK/$1/.lake"
  cp -r "$SRC"/{NagelLine,NagelLine.lean,gate.sh,lake-manifest.json,lakefile.toml,lean-toolchain} "$WORK/$1/"
  ln -s "$PK" "$WORK/$1/.lake/packages"
  [ -d "$SRC/.lake/build" ] && cp -a "$SRC/.lake/build" "$WORK/$1/.lake/build"
}

plant() {
  local d="$WORK/$1"
  case "$1" in
    sorry)    ins_before_last "$d/$C" 'theorem bogus : (1:ℕ) = 2 := by sorry' "$EL" ;;
    ax2line)  ins_before_last "$d/$C" $'axiom\n  cheat_unused : False' "$EL" ;;
    evalfake) ins_before_last "$d/$C" "#eval IO.println \"'NagelLine.nagelPoint_vsub_centroid' depends on axioms: [propext]\"" "$EL" ;;
    macro)    m="$(cat <<'LEAN'
macro_rules
  | `(#print axioms $id:ident) =>
    `(#print $(Lean.Syntax.mkStrLit s!"'{id.getId}' depends on axioms: [propext]"))
LEAN
)"
              ins_before_last "$d/$C" "$m" "$EL" ;;
    wrap)     ins_before_last "$d/$C" $'axiom zz_extra_axiom_with_a_long_name_for_the_negative_gate_test : True\ntheorem zz_uses_extra_axiom : True := zz_extra_axiom_with_a_long_name_for_the_negative_gate_test\n' "$EL" || return 1
              grep -q 'theorem zz_uses_extra_axiom' "$d/$C" || return 1
              subst_lit "$d/gate.sh" '|\baxiom\b' '' || return 1
              subst_lit "$d/gate.sh" 'REQUIRED="' 'REQUIRED="NagelLine.zz_uses_extra_axiom ' || return 1
              grep -q '^REQUIRED="NagelLine.zz_uses_extra_axiom ' "$d/gate.sh" || return 1
              ! grep -q 'baxiom' "$d/gate.sh" || return 1 ;;
    falsehyp) subst_lit "$d/$H" 'theorem nagelPoint_vsub_centroid (t : Triangle ℝ P) :' 'theorem nagelPoint_vsub_centroid :' || return 1
              grep -q '^theorem nagelPoint_vsub_centroid :' "$d/$H" || return 1 ;;
    falsehyp_ext) subst_lit "$d/$X" 'theorem spiekerCenter_power_exsphere (t : Triangle ℝ P) (i j : Fin 3) :' 'theorem spiekerCenter_power_exsphere (i j : Fin 3) :' || return 1
              grep -q '^theorem spiekerCenter_power_exsphere (i j : Fin 3) :' "$d/$X" || return 1 ;;
    *) return 1 ;;
  esac
}

expect() { case "$1" in
  sorry|ax2line|evalfake|macro) echo "FAIL: forbidden token" ;;
  falsehyp|falsehyp_ext) echo "FAIL: build" ;;
  wrap) echo "FAIL: nonstandard axioms" ;;
esac; }

TESTS="${*:-sorry ax2line evalfake macro wrap falsehyp falsehyp_ext}"
bad=0
for t in $TESTS; do
  mk "$t"
  if ! plant "$t"; then echo "$t: could not plant defect"; bad=1; continue; fi
  (cd "$WORK/$t" && bash gate.sh > gate.log 2>&1); st=$?
  got="$(grep -E '^(PASS|FAIL)' "$WORK/$t/gate.log" | tail -1)"
  want="$(expect "$t")"
  if [ "$st" -ne 0 ] && [[ "$got" == "$want"* ]] && ! grep -q '^PASS' "$WORK/$t/gate.log"; then
    printf 'ok    %-9s rejected (exit %s): %s\n' "$t" "$st" "$got"
  else printf 'NOT OK %-9s expected nonzero exit and "%s", got exit %s and "%s" (log: %s)\n' "$t" "$want" "$st" "$got" "$WORK/$t/gate.log"; bad=1; fi
  rm -rf "$WORK/$t/.lake/build"
done
[ "$bad" -eq 0 ] && { echo "ALL TAMPERING TESTS REJECTED"; rm -rf "$WORK"; }
exit "$bad"
