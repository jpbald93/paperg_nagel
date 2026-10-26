# NagelLine — the Nagel line family in Lean 4 / Mathlib

**Paper:** J. Bald, *Triangle centres in Lean 4: the Nagel line family and the symmedian and Brocard
points* (2026). The paper states every theorem in prose with all hypotheses and reports the
verification. Companion repository: https://github.com/jpbald93/paperg_brocard.

**Toolchain:** Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (see `lake-manifest.json`).
**Check:** `lake build && bash gate.sh` prints `PASS (151 declarations, standard axioms only)`;
`bash tests/tamper.sh` prints `ALL TAMPERING TESTS REJECTED`. **Licence:** Apache-2.0.

Formalises, for an arbitrary non-degenerate triangle `t : Affine.Triangle ℝ P` in a real inner
product space (no dimension assumption), the Gergonne point, the Nagel point, the Nagel line and
the Spieker centre. All statements are about Mathlib's own `incenter`, `excenter`, `touchpoint`,
`medial` and `Finset.univ.centroid`. The only hypothesis is the triangle `t` itself.

Notation: `A, B, C = t.points 0, 1, 2`; `a = dist B C` (`NagelLine.sideA`), `b = dist C A`,
`c = dist A B`, `s = (a+b+c)/2` (`NagelLine.semiperimeter`); `NagelLine.side t i` is the side
opposite vertex `i`.

## Definitions (`NagelLine/Basic.lean`)

| Lean name | Meaning | line |
|---|---|---|
| `Affine.Triangle.nagelPoint` | affine combination of A, B, C with weights `(s-a)/s, (s-b)/s, (s-c)/s` | Basic.lean:267 |
| `Affine.Triangle.gergonnePoint` | weights `1/(s-a), 1/(s-b), 1/(s-c)`, normalised | Basic.lean:271 |
| `Affine.Triangle.spiekerCenter` | `t.medial.incenter` (incentre of Mathlib's medial triangle) | Basic.lean:276 |

## Main theorems (`NagelLine/Main.lean`)

| Plain English | Lean name | line |
|---|---|---|
| A1: for each vertex i, the Gergonne point lies on the line through vertex i and the incircle's contact point on the opposite side | `NagelLine.gergonnePoint_mem_cevian` | Main.lean:290 |
| A1 corollary: the three Gergonne cevians are concurrent | `NagelLine.gergonne_cevians_concurrent` | Main.lean:328 |
| A2: for each vertex i, the Nagel point lies on the line through vertex i and the contact point of the excircle opposite i with the opposite side | `NagelLine.nagelPoint_mem_cevian` | Main.lean:334 |
| A2 corollary: the three Nagel cevians are concurrent | `NagelLine.nagel_cevians_concurrent` | Main.lean:357 |
| A3(i): `N − G = 2 (G − I)` | `NagelLine.nagelPoint_vsub_centroid` | Main.lean:362 |
| A3(i): I, G, N are collinear (Nagel line) | `NagelLine.collinear_incenter_centroid_nagelPoint` | Main.lean:373 |
| A3(ii): the incentre of the medial triangle is the midpoint of I and N | `NagelLine.medial_incenter_eq_midpoint` | Main.lean:385 |
| A3(ii): the Spieker centre lies on the Nagel line | `NagelLine.collinear_spiekerCenter_incenter_nagelPoint` | Main.lean:408 |

## Bridge lemmas (Mathlib object ↔ explicit weights)

| Plain English | Lean name | line |
|---|---|---|
| `s−a, s−b, s−c > 0` (strict triangle inequality, derived from affine independence via heights) | `NagelLine.s_sub_a_pos`, `s_sub_b_pos`, `s_sub_c_pos` | Basic.lean:189/194/202 |
| `(height_i · side_i)² = 4 s(s−a)(s−b)(s−c)`-type Heron identity | `NagelLine.height0_sq` … `height2_sq`, `heron_factor` | Basic.lean:115–161 |
| Mathlib's `excenterWeights ∅` = `side i / 2s` | `NagelLine.incenter_weights` | Basic.lean:219 |
| Mathlib's `excenterWeights {i}` = `±side j / 2(s − side i)` | `NagelLine.excenter_weights` | Basic.lean:238 |
| incentre / excentre as explicit affine combinations | `NagelLine.incenter_eq_affineCombination`, `excenter_singleton_eq_affineCombination` | Main.lean:68/75 |
| incircle contact points: `touchpoint ∅ 0 = lineMap B C ((s−b)/a)`, `touchpoint ∅ 1 = lineMap C A ((s−c)/b)`, `touchpoint ∅ 2 = lineMap A B ((s−a)/c)` | `NagelLine.touchpoint_empty_zero/one/two` | Main.lean:94/105/117 |
| excircle contact points: `touchpoint {0} 0 = lineMap B C ((s−c)/a)`, `touchpoint {1} 1 = lineMap C A ((s−a)/b)`, `touchpoint {2} 2 = lineMap A B ((s−b)/c)` | `NagelLine.touchpoint_singleton_zero/one/two` | Main.lean:129/141/155 |
| the excircle contact points lie strictly inside the sides (so `touchpoint {i} i` is the contact with the segment, not its extension) | `NagelLine.sbtw_touchpoint_singleton_zero/one/two` | Main.lean:170/179/188 |
| sides of the medial triangle are half the sides | `NagelLine.medial_sideA/B/C` | Main.lean:266–268 |

Mathlib conventions used: `excenter {i}` is the excentre opposite vertex `i`
(`excenterWeightsUnnorm` puts the minus sign on index `i`); `touchpoint signs i` is the orthogonal
projection of that excentre onto `faceOpposite i`, i.e. the line through the other two vertices;
`medial.points i = faceOppositeCentroid i`, the midpoint of the side opposite `i`.

## Proof method

Barycentric certificates: heights are computed by projecting onto the face line and the
Heron polynomial, which identifies Mathlib's inverse-height weights with `a : b : c`.
Contact points are characterised by `coe_orthogonalProjection_eq_iff_mem` with an explicit
parameter. Everything then reduces to rational identities, closed after the Ravi substitution
`a = y+z, b = x+z, c = x+y` by `field_simp; ring` / `match_scalars`.

## Build / check

From the repository root (Lean toolchain from `lean-toolchain`, Mathlib pinned in
`lake-manifest.json`; `.lake/packages` must already hold a built Mathlib):

    lake build                 # builds the library
    bash gate.sh               # forbidden-token scan + build + #print axioms for 77 declarations
    bash tests/tamper.sh       # plants 7 defects in scratch copies; each must be rejected

Expected outputs: `PASS (77 declarations, standard axioms only)` and
`ALL TAMPERING TESTS REJECTED`.

## Extensions (`NagelLine/Extensions.lean`)

Same setting, and again the only hypothesis is the triangle `t`. `O = t.circumcenter`,
`H = t.orthocenter` (Mathlib), `G = Finset.univ.centroid ℝ t.points`.

### Definitions

| Lean name | Meaning | line |
|---|---|---|
| `Affine.Triangle.deLongchampsPoint` | `L = 2 • (O -ᵥ H) +ᵥ H`, the reflection of `H` in `O` | Extensions.lean:24 |
| `Affine.Triangle.anticomplementary` | the triangle `t.map (homothety G (-2))`, with vertices `B + C − A`, `C + A − B`, `A + B − C`. It is a genuine `Affine.Triangle ℝ P`: affine independence comes from `Simplex.map` together with `homothety_injective` | Extensions.lean:30 |

### Theorems

| Plain English | Lean name | line |
|---|---|---|
| C1: `O` is the midpoint of `H` and `L` | `NagelLine.midpoint_orthocenter_deLongchampsPoint` | Extensions.lean:228 |
| C1: `L`, `O`, `H` are collinear | `NagelLine.collinear_deLongchampsPoint_circumcenter_orthocenter` | Extensions.lean:237 |
| C1: `L` lies on the Euler line, `Collinear ℝ {G, O, L}` | `NagelLine.collinear_centroid_circumcenter_deLongchampsPoint` | Extensions.lean:249 |
| C1: `L` is the orthocentre of the anticomplementary triangle | `NagelLine.anticomplementary_orthocenter` | Extensions.lean:261 |
| C2: the Nagel point of the medial triangle is the incentre | `NagelLine.medial_nagelPoint` | Extensions.lean:274 |
| C2: on each side, the incircle and excircle contact points are symmetric about the midpoint of that side (`midpoint (touchpoint ∅ i) (touchpoint {i} i) = midpoint` of the side opposite `i`) | `NagelLine.midpoint_touchpoint_zero/one/two` | Extensions.lean:297/308/319 |
| C3: the Nagel point is the incentre of the anticomplementary triangle | `NagelLine.nagelPoint_eq_anticomplementary_incenter` | Extensions.lean:332 |
| C4: the Spieker centre has the same power `dist S J_i ² − r_i²` with respect to every excircle, i.e. it is their radical centre | `NagelLine.spiekerCenter_power_exsphere` | Extensions.lean:357 |
| C4, explicit value: that power equals `(s² + (s−a)(s−b)(s−c)/s) / 4`, i.e. `(s² + r²)/4` | `NagelLine.spiekerCenter_power_exsphere_eq` | Extensions.lean:201 |

### Bridge lemmas

| Plain English | Lean name | line |
|---|---|---|
| anticomplementary vertices as `-2 • (P_i -ᵥ G) +ᵥ G`, and explicitly as `B + C − A` etc. | `NagelLine.anticomplementary_points`, `anticomplementary_points_zero/one/two` | Extensions.lean:57/63/71/79 |
| the anticomplementary triangle has the same centroid, and its medial triangle is `t` | `NagelLine.centroid_anticomplementary`, `anticomplementary_medial` | Extensions.lean:86/93 |
| `H − O = 3 (G − O)` and `L − O = 3 (O − G)` | `NagelLine.orthocenter_vsub_circumcenter`, `deLongchampsPoint_vsub_circumcenter` | Extensions.lean:104/108 |
| the circumcentre of the anticomplementary triangle is `H` (via `eq_circumcenter_of_dist_eq` with radius `2R`) | `NagelLine.anticomplementary_circumcenter` | Extensions.lean:116 |
| `∑ excenterWeightsUnnorm {i} = 2(s − side i)/(2Δ)`, so `exradius {i}² = 4s(s−a)(s−b)(s−c)/(2(s − side i))²` | `NagelLine.sum_excenterWeightsUnnorm_singleton`, `exradius_singleton_sq` | Extensions.lean:160/172 |
| excentre and Spieker centre in coordinates relative to `A` | `NagelLine.excenter_singleton_vsub_zero`, `spiekerCenter_vsub_zero` | Extensions.lean:181/189 |
| squared distance from the coordinates relative to `A`; generic helpers | `NagelLine.dist_sq_of_vsub`, `norm_comb_sq`, `midpoint_lineMap_lineMap` | Extensions.lean:145/41/47 |

Statement note: C2 is written as `Triangle.nagelPoint t.medial = t.incenter`, not
`t.medial.nagelPoint`. `Simplex.medial` returns a `Simplex ℝ P 2`, and field notation looks in
`Affine.Simplex.*`, so `t.medial.nagelPoint` does not elaborate. Both forms denote the same term.

With the extensions, the gate checks 77 declarations (`PASS (77 declarations, standard axioms only)`).
The tamper suite has 7 cases. The new `falsehyp_ext` case removes the binder `(t : Triangle ℝ P)`
from `spiekerCenter_power_exsphere` and must fail with `FAIL: build`.

## Layer 15 (classical statements) (`NagelLine/L15Classical.lean`)

Namespace `NagelLine.Classical`. The basic definitions of the classical statement file
`PaperGClassical.lean` (sha256 prefix `2bb545d76d505fe0`) are copied verbatim, with `Pt` written
out as `EuclideanSpace ℝ (Fin 2)`. Each `cov_*` theorem has the classical textbook statement as its
type and is proved from the library theorems above.

### Classical statements covered

| Plain English | Lean name |
|---|---|
| N1: the Gergonne cevians (vertex to incircle contact point) are concurrent | `NagelLine.Classical.cov_N1` |
| N2a: the Nagel cevians (vertex to excircle contact point) are concurrent | `NagelLine.Classical.cov_N2a` |
| N2b: the excircle opposite `A` touches `BC` at `D` with `BD = s − c` and `CD = s − b` | `NagelLine.Classical.cov_N2b` |
| N3: Nagel line. `I`, `G`, `Na` are collinear, `G` lies between `I` and `Na`, and `GNa = 2·IG` | `NagelLine.Classical.cov_N3` |
| N4: the Spieker centre is the midpoint of `I` and `Na`, and `I`, `G`, `Na`, `Sp` are collinear | `NagelLine.Classical.cov_N4` |
| N5: the incircle and excircle contact points on `BC` are symmetric about its midpoint (all three sides: `cov_N5_all`) | `NagelLine.Classical.cov_N5`, `cov_N5_all` |
| N6a: the Nagel point of the medial triangle is the incentre | `NagelLine.Classical.cov_N6a` |
| N6b: the Nagel point is the incentre of the anticomplementary triangle | `NagelLine.Classical.cov_N6b` |
| N7: `O`, `G`, `H` and the de Longchamps point `L` are collinear, and `L` is the orthocentre of the anticomplementary triangle | `NagelLine.Classical.cov_N7` |
| N8: the Spieker centre has equal power with respect to the three excircles | `NagelLine.Classical.cov_N8` |

### New proofs

| Plain English | Lean name |
|---|---|
| two cevians from different vertices meet in at most one point | `NagelLine.Classical.cevian_unique` |
| uniqueness of the Nagel point: any common point of the Nagel cevians is the library's `nagelPoint` | `NagelLine.Classical.nagel_unique` |
| the medial triangle of a non-degenerate triangle is non-degenerate (the classical extra hypothesis is redundant) | `NagelLine.Classical.medial_indep` |
| the anticomplementary triangle of a non-degenerate triangle is non-degenerate (the classical extra hypothesis is redundant) | `NagelLine.Classical.anti_indep` |
| bridge lemmas: the textbook excentre `−a : b : c`, the contact points defined as perpendicular feet, and the classical medial/anticomplementary triangles equal the Mathlib/library objects | `exA0/1/2`, `exC0/1/2`, `inA/B/C_eq`, `medial_eq`, `anti_eq`, `deLongchamps_eq`, … |

With Layer 15 the gate checks 149 declarations (`PASS (149 declarations, standard axioms only)`).

## Inradius form (`NagelLine/Inradius.lean`)

| Plain English | Lean name | line |
|---|---|---|
| Mathlib's inradius satisfies `r² = (s−a)(s−b)(s−c)/s` | `NagelLine.inradius_sq` | Inradius.lean:19 |
| the common power of the Spieker centre with respect to the excircles is `(s² + r²)/4` | `NagelLine.spiekerCenter_power_exsphere_eq_inradius` | Inradius.lean:40 |

With these the gate checks 151 declarations (`PASS (151 declarations, standard axioms only)`).
