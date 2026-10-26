#!/bin/bash
# Gate for the NagelLine Lean formalisation. Passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `#eval`, `run_cmd`,
#    `initialize`, `IO`, `set_option`, or syntax-extension commands (which could redefine
#    `#print axioms`);
#  * the library builds without errors;
#  * the gate itself generates the `#print axioms` report for each REQUIRED theorem;
#  * each REQUIRED theorem uses only Lean's standard axioms (propext, Classical.choice, Quot.sound).
# SCAFFOLD=1 skips the forbidden-token check and also tolerates `sorryAx`, so a partially
# finished development can be checked while it still contains `sorry`.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="NagelLine"
LIB="NagelLine"
REQUIRED="NagelLine.sideA NagelLine.sideB NagelLine.sideC NagelLine.semiperimeter NagelLine.heronPoly NagelLine.dblArea NagelLine.side NagelLine.proj_eq_lineMap NagelLine.height_sq_mul NagelLine.height0_sq NagelLine.height1_sq NagelLine.height2_sq NagelLine.height_eq NagelLine.heron_factor NagelLine.semiperimeter_pos NagelLine.s_sub_a_pos NagelLine.s_sub_b_pos NagelLine.s_sub_c_pos NagelLine.incenter_weights NagelLine.excenter_weights NagelLine.projSpan0 NagelLine.projSpan1 NagelLine.projSpan2 NagelLine.incenter_eq_affineCombination NagelLine.excenter_singleton_eq_affineCombination NagelLine.touchpoint_empty_zero NagelLine.touchpoint_empty_one NagelLine.touchpoint_empty_two NagelLine.touchpoint_singleton_zero NagelLine.touchpoint_singleton_one NagelLine.touchpoint_singleton_two NagelLine.sbtw_touchpoint_singleton_zero NagelLine.sbtw_touchpoint_singleton_one NagelLine.sbtw_touchpoint_singleton_two NagelLine.medial_sideA NagelLine.medial_sideB NagelLine.medial_sideC NagelLine.gergonnePoint_mem_cevian NagelLine.gergonne_cevians_concurrent NagelLine.nagelPoint_mem_cevian NagelLine.nagel_cevians_concurrent NagelLine.nagelPoint_vsub_centroid NagelLine.collinear_incenter_centroid_nagelPoint NagelLine.medial_incenter_eq_midpoint NagelLine.collinear_spiekerCenter_incenter_nagelPoint Affine.Triangle.nagelPoint Affine.Triangle.gergonnePoint Affine.Triangle.spiekerCenter Affine.Triangle.deLongchampsPoint Affine.Triangle.anticomplementary NagelLine.norm_comb_sq NagelLine.midpoint_lineMap_lineMap NagelLine.anticomplementary_points NagelLine.anticomplementary_points_zero NagelLine.anticomplementary_points_one NagelLine.anticomplementary_points_two NagelLine.centroid_anticomplementary NagelLine.anticomplementary_medial NagelLine.orthocenter_vsub_circumcenter NagelLine.deLongchampsPoint_vsub_circumcenter NagelLine.anticomplementary_circumcenter NagelLine.dist_sq_of_vsub NagelLine.sum_excenterWeightsUnnorm_singleton NagelLine.exradius_singleton_sq NagelLine.excenter_singleton_vsub_zero NagelLine.spiekerCenter_vsub_zero NagelLine.spiekerCenter_power_exsphere_eq NagelLine.inradius_sq NagelLine.spiekerCenter_power_exsphere_eq_inradius NagelLine.midpoint_orthocenter_deLongchampsPoint NagelLine.collinear_deLongchampsPoint_circumcenter_orthocenter NagelLine.collinear_centroid_circumcenter_deLongchampsPoint NagelLine.anticomplementary_orthocenter NagelLine.medial_nagelPoint NagelLine.midpoint_touchpoint_zero NagelLine.midpoint_touchpoint_one NagelLine.midpoint_touchpoint_two NagelLine.nagelPoint_eq_anticomplementary_incenter NagelLine.spiekerCenter_power_exsphere NagelLine.l14_gergonne NagelLine.l14_nagel NagelLine.l14_nagelLine NagelLine.l14_spieker NagelLine.l14_deLongchamps NagelLine.l14_medial_nagel NagelLine.l14_isotomic NagelLine.l14_nagel_anticomplementary NagelLine.l14_spieker_radical NagelLine.l14w_nagel NagelLine.l14w_medial_nagel NagelLine.l14w_nagel_anticomplementary NagelLine.l14w_spieker_radical NagelLine.l14w_deLongchamps NagelLine.Classical.ClassicalTri NagelLine.Classical.ClassicalBary NagelLine.Classical.ClassicalSemiperimeter NagelLine.Classical.ClassicalArea NagelLine.Classical.ClassicalCentroid NagelLine.Classical.ClassicalExcenterA NagelLine.Classical.ClassicalExContactA NagelLine.Classical.ClassicalExradiusA NagelLine.Classical.ClassicalInContactA NagelLine.Classical.ClassicalInContactB NagelLine.Classical.ClassicalInContactC NagelLine.Classical.ClassicalBisectorPoint NagelLine.Classical.ClassicalIsogonalLine NagelLine.Classical.ClassicalSymmedian NagelLine.Classical.ClassicalIsogonalConj NagelLine.Classical.ClassicalFoot NagelLine.Classical.ClassicalPedalCentroid NagelLine.Classical.ClassicalAnticompl NagelLine.Classical.proj_congr NagelLine.Classical.bary_lin NagelLine.Classical.sA NagelLine.Classical.sB NagelLine.Classical.sC NagelLine.Classical.inA_eq NagelLine.Classical.inB_eq NagelLine.Classical.inC_eq NagelLine.Classical.tri_pos NagelLine.Classical.inv_helper NagelLine.Classical.exA0 NagelLine.Classical.exA1 NagelLine.Classical.exA2 NagelLine.Classical.exC0 NagelLine.Classical.exC1 NagelLine.Classical.exC2 NagelLine.Classical.cevian_unique NagelLine.Classical.nagel_unique NagelLine.Classical.centroid_lin NagelLine.Classical.medial_points_eq NagelLine.Classical.medial_indep NagelLine.Classical.medial_eq NagelLine.Classical.anti_points_eq NagelLine.Classical.anti_indep NagelLine.Classical.anti_eq NagelLine.Classical.col_of_mem NagelLine.Classical.centroid_eq_lineMap NagelLine.Classical.O_H_lineMap NagelLine.Classical.deLongchamps_eq NagelLine.Classical.cov_N1 NagelLine.Classical.cov_N2a NagelLine.Classical.cov_N2b NagelLine.Classical.cov_N3 NagelLine.Classical.cov_N4 NagelLine.Classical.cov_N5 NagelLine.Classical.cov_N5_all NagelLine.Classical.cov_N6a NagelLine.Classical.cov_N6b NagelLine.Classical.cov_N7 NagelLine.Classical.cov_N8"
SOURCES="NagelLine/*.lean NagelLine.lean"
[ -e .lake/packages/mathlib ] || { echo "FAIL: Mathlib packages missing (run setup by hand)"; exit 1; }
if [ "${SCAFFOLD:-0}" != "1" ]; then
  if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
    echo "FAIL: forbidden token"; exit 1; fi
fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
root=$(lake env lean "$LIB.lean" 2>&1) || { printf '%s\n' "$root"; echo "FAIL: build (root file)"; exit 1; }
chk=".gatecheck_$$.lean"
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  te=$(printf '%s' "$t" | sed 's/[.]/\\./g')
  c=$(printf '%s\n' "$reports" | grep -cE "^'$te' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
if [ "${SCAFFOLD:-0}" = "1" ]; then ALLOW='^(propext|Classical\.choice|Quot\.sound|sorryAx)$'; else ALLOW='^(propext|Classical\.choice|Quot\.sound)$'; fi
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE "$ALLOW")
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n declarations, standard axioms only)"
