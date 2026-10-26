import NagelLine.Basic

/-!
# The Nagel line family

Bridges from Mathlib's `incenter`, `excenter`, `touchpoint`, `medial` and `centroid` to explicit
barycentric weights, and the main theorems: the Gergonne and Nagel cevians are concurrent, the
Nagel line `I, G, N` with `N - G = 2 (G - I)`, and the Spieker centre (incentre of the medial
triangle) is the midpoint of `I` and `N`.
-/

open Affine EuclideanGeometry AffineMap
open scoped RealInnerProductSpace

namespace NagelLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## Generic vector lemmas -/

lemma ac_vsub_base (p : Fin 3 → P) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) (b : P) :
    Finset.univ.affineCombination ℝ p w -ᵥ b =
      w 0 • (p 0 -ᵥ b) + w 1 • (p 1 -ᵥ b) + w 2 • (p 2 -ᵥ b) := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ w _ hw b, vadd_vsub,
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three]

lemma mem_line_lineMap {X Y Z Q : P} {α β r k : ℝ}
    (hQ : Q -ᵥ X = α • (Y -ᵥ X) + β • (Z -ᵥ X)) (h1 : α = k * (1 - r)) (h2 : β = k * r) :
    Q ∈ line[ℝ, X, lineMap Y Z r] := by
  have hQ' : Q = lineMap X (lineMap Y Z r) k := by
    rw [lineMap_apply X, eq_vadd_iff_vsub_eq, hQ, lineMap_apply Y, vadd_vsub_assoc,
      ← vsub_sub_vsub_cancel_right Z Y X, h1, h2]
    module
  rw [hQ']
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

lemma inner_cond {X Y Z J : P} {wX wZ r : ℝ} (hJ : J -ᵥ Y = wX • (X -ᵥ Y) + wZ • (Z -ᵥ Y))
    (h : wX * ((dist Y X ^ 2 + dist Y Z ^ 2 - dist X Z ^ 2) / 2) + wZ * dist Y Z ^ 2 =
      r * dist Y Z ^ 2) :
    ⟪J -ᵥ Y, Z -ᵥ Y⟫ = r * dist Y Z ^ 2 := by
  rw [hJ, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_vsub_vsub_eq,
    real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V, dist_comm Z Y]
  exact h

variable (t : Triangle ℝ P)

/-- Ravi substitution: `a = y + z`, `b = x + z`, `c = x + y`, `s = x + y + z` with `x, y, z > 0`. -/
lemma ravi : ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ sideA t = y + z ∧ sideB t = x + z ∧
    sideC t = x + y ∧ semiperimeter t = x + y + z :=
  ⟨_, _, _, s_sub_a_pos t, s_sub_b_pos t, s_sub_c_pos t, by unfold semiperimeter; ring,
    by unfold semiperimeter; ring, by unfold semiperimeter; ring, by unfold semiperimeter; ring⟩

lemma d10 : dist (t.points 1) (t.points 0) = sideC t := dist_comm _ _
lemma d20 : dist (t.points 2) (t.points 0) = sideB t := rfl
lemma d21 : dist (t.points 2) (t.points 1) = sideA t := dist_comm _ _
lemma d01 : dist (t.points 0) (t.points 1) = sideC t := rfl
lemma d02 : dist (t.points 0) (t.points 2) = sideB t := dist_comm _ _
lemma d12 : dist (t.points 1) (t.points 2) = sideA t := rfl

lemma side0 : side t 0 = sideA t := rfl
lemma side1 : side t 1 = sideB t := rfl
lemma side2 : side t 2 = sideC t := rfl

/-! ## Bridges: incentre and excentres as explicit affine combinations -/

/-- The incentre has barycentric weights `a : b : c` (normalised by `2s`). -/
theorem incenter_eq_affineCombination :
    t.incenter = Finset.univ.affineCombination ℝ t.points
      (fun i ↦ side t i / (2 * semiperimeter t)) := by
  rw [Simplex.incenter_eq_affineCombination, incenter_weights]

/-- The excentre opposite vertex `i` (Mathlib's `excenter {i}`) has weights
`-a : b : c` (for `i = 0`, and analogously), normalised by `2 (s - side i)`. -/
theorem excenter_singleton_eq_affineCombination (i : Fin 3) :
    t.excenter {i} = Finset.univ.affineCombination ℝ t.points
      (fun j ↦ (if j = i then -1 else 1) * side t j / (2 * (semiperimeter t - side t i))) := by
  rw [Simplex.excenter_eq_affineCombination, excenter_weights]

lemma sum_in : ∑ i, side t i / (2 * semiperimeter t) = 1 := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [Fin.sum_univ_three, side0, side1, side2, ha, hb, hc, hs]
  field_simp; ring

lemma sum_ex (i : Fin 3) :
    ∑ j, (if j = i then -1 else 1) * side t j / (2 * (semiperimeter t - side t i)) = 1 := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [side0, side1, side2, ha, hb, hc, hs] <;> field_simp <;> ring

/-! ## Bridges: the contact points -/

/-- Incircle contact point on `BC`: `lineMap B C ((s - b) / a)`. -/
theorem touchpoint_empty_zero : t.touchpoint ∅ 0 =
    lineMap (t.points 1) (t.points 2) ((semiperimeter t - sideB t) / sideA t) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  refine projSpan0 t _ _ (inner_cond (X := t.points 0) (wX := side t 0 / (2 * semiperimeter t))
    (wZ := side t 2 / (2 * semiperimeter t)) ?_ ?_)
  · rw [show t.excenter ∅ = t.incenter from rfl, incenter_eq_affineCombination, ac_vsub_base _ _ (sum_in t)]
    simp only [vsub_self, smul_zero, add_zero]
  · rw [d10, d12, d02, side0, side2, ha, hb, hc, hs]
    field_simp; ring

/-- Incircle contact point on `CA`: `lineMap C A ((s - c) / b)`. -/
theorem touchpoint_empty_one : t.touchpoint ∅ 1 =
    lineMap (t.points 2) (t.points 0) ((semiperimeter t - sideC t) / sideB t) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  refine projSpan1 t _ _ (inner_cond (X := t.points 1) (wX := side t 1 / (2 * semiperimeter t))
    (wZ := side t 0 / (2 * semiperimeter t)) ?_ ?_)
  · rw [show t.excenter ∅ = t.incenter from rfl, incenter_eq_affineCombination, ac_vsub_base _ _ (sum_in t)]
    simp only [vsub_self, smul_zero, add_zero]
    abel
  · rw [d21, d20, d10, side0, side1, ha, hb, hc, hs]
    field_simp; ring

/-- Incircle contact point on `AB`: `lineMap A B ((s - a) / c)`. -/
theorem touchpoint_empty_two : t.touchpoint ∅ 2 =
    lineMap (t.points 0) (t.points 1) ((semiperimeter t - sideA t) / sideC t) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  refine projSpan2 t _ _ (inner_cond (X := t.points 2) (wX := side t 2 / (2 * semiperimeter t))
    (wZ := side t 1 / (2 * semiperimeter t)) ?_ ?_)
  · rw [show t.excenter ∅ = t.incenter from rfl, incenter_eq_affineCombination, ac_vsub_base _ _ (sum_in t)]
    simp only [vsub_self, smul_zero, zero_add]
    abel
  · rw [d02, d01, d21, side1, side2, ha, hb, hc, hs]
    field_simp; ring

/-- Contact point of the `A`-excircle with `BC`: `lineMap B C ((s - c) / a)`. -/
theorem touchpoint_singleton_zero : t.touchpoint {0} 0 =
    lineMap (t.points 1) (t.points 2) ((semiperimeter t - sideC t) / sideA t) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  refine projSpan0 t _ _ (inner_cond (X := t.points 0)
    (wX := -side t 0 / (2 * (semiperimeter t - side t 0)))
    (wZ := side t 2 / (2 * (semiperimeter t - side t 0))) ?_ ?_)
  · rw [excenter_singleton_eq_affineCombination, ac_vsub_base _ _ (sum_ex t 0)]
    simp
  · rw [d10, d12, d02, side0, side2, ha, hb, hc, hs]
    ring_nf; field_simp; ring

/-- Contact point of the `B`-excircle with `CA`: `lineMap C A ((s - a) / b)`. -/
theorem touchpoint_singleton_one : t.touchpoint {1} 1 =
    lineMap (t.points 2) (t.points 0) ((semiperimeter t - sideA t) / sideB t) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  refine projSpan1 t _ _ (inner_cond (X := t.points 1)
    (wX := -side t 1 / (2 * (semiperimeter t - side t 1)))
    (wZ := side t 0 / (2 * (semiperimeter t - side t 1))) ?_ ?_)
  · rw [excenter_singleton_eq_affineCombination, ac_vsub_base _ _ (sum_ex t 1)]
    simp only [vsub_self, smul_zero, add_zero]
    simp
    abel
  · rw [d21, d20, d10, side0, side1, ha, hb, hc, hs]
    ring_nf; field_simp; ring

/-- Contact point of the `C`-excircle with `AB`: `lineMap A B ((s - b) / c)`. -/
theorem touchpoint_singleton_two : t.touchpoint {2} 2 =
    lineMap (t.points 0) (t.points 1) ((semiperimeter t - sideB t) / sideC t) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  refine projSpan2 t _ _ (inner_cond (X := t.points 2)
    (wX := -side t 2 / (2 * (semiperimeter t - side t 2)))
    (wZ := side t 1 / (2 * (semiperimeter t - side t 2))) ?_ ?_)
  · rw [excenter_singleton_eq_affineCombination, ac_vsub_base _ _ (sum_ex t 2)]
    simp only [vsub_self, smul_zero, zero_add]
    simp
    abel
  · rw [d02, d01, d21, side1, side2, ha, hb, hc, hs]
    ring_nf; field_simp; ring

/-- The `A`-excircle touches `BC` strictly between `B` and `C` (so `touchpoint {0} 0` is the
contact with the segment `BC`, not with an extension). -/
theorem sbtw_touchpoint_singleton_zero :
    Sbtw ℝ (t.points 1) (t.touchpoint {0} 0) (t.points 2) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [touchpoint_singleton_zero, sbtw_lineMap_iff]
  refine ⟨fun h ↦ by simpa using t.independent.injective h, ?_, ?_⟩ <;>
    rw [ha, hc, hs] <;> [skip; rw [div_lt_one (by positivity)]] <;>
    [exact div_pos (by linarith) (by linarith); linarith]

/-- The `B`-excircle touches `CA` strictly between `C` and `A`. -/
theorem sbtw_touchpoint_singleton_one :
    Sbtw ℝ (t.points 2) (t.touchpoint {1} 1) (t.points 0) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [touchpoint_singleton_one, sbtw_lineMap_iff]
  refine ⟨fun h ↦ by simpa using t.independent.injective h, ?_, ?_⟩ <;>
    rw [ha, hb, hs] <;> [skip; rw [div_lt_one (by positivity)]] <;>
    [exact div_pos (by linarith) (by linarith); linarith]

/-- The `C`-excircle touches `AB` strictly between `A` and `B`. -/
theorem sbtw_touchpoint_singleton_two :
    Sbtw ℝ (t.points 0) (t.touchpoint {2} 2) (t.points 1) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [touchpoint_singleton_two, sbtw_lineMap_iff]
  refine ⟨fun h ↦ by simpa using t.independent.injective h, ?_, ?_⟩ <;>
    rw [hb, hc, hs] <;> [skip; rw [div_lt_one (by positivity)]] <;>
    [exact div_pos (by linarith) (by linarith); linarith]

/-! ## Cevian criteria -/

lemma cevian0 (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) (r : ℝ) (h : w 1 * r = w 2 * (1 - r)) :
    Finset.univ.affineCombination ℝ t.points w ∈
      line[ℝ, t.points 0, lineMap (t.points 1) (t.points 2) r] := by
  refine mem_line_lineMap (α := w 1) (β := w 2) (k := w 1 + w 2) ?_ ?_ ?_
  · rw [ac_vsub_base _ _ hw]; simp
  · linear_combination h
  · linear_combination -h

lemma cevian1 (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) (r : ℝ) (h : w 2 * r = w 0 * (1 - r)) :
    Finset.univ.affineCombination ℝ t.points w ∈
      line[ℝ, t.points 1, lineMap (t.points 2) (t.points 0) r] := by
  refine mem_line_lineMap (α := w 2) (β := w 0) (k := w 2 + w 0) ?_ ?_ ?_
  · rw [ac_vsub_base _ _ hw]; simp only [vsub_self, smul_zero, add_zero]; abel
  · linear_combination h
  · linear_combination -h

lemma cevian2 (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) (r : ℝ) (h : w 0 * r = w 1 * (1 - r)) :
    Finset.univ.affineCombination ℝ t.points w ∈
      line[ℝ, t.points 2, lineMap (t.points 0) (t.points 1) r] := by
  refine mem_line_lineMap (α := w 0) (β := w 1) (k := w 0 + w 1) ?_ ?_ ?_
  · rw [ac_vsub_base _ _ hw]; simp only [vsub_self, smul_zero, add_zero]
  · linear_combination h
  · linear_combination -h

lemma sum_nagel : ∑ i, (semiperimeter t - side t i) / semiperimeter t = 1 := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [Fin.sum_univ_three, side0, side1, side2, ha, hb, hc, hs]
  field_simp; ring

lemma sum_gergonne :
    ∑ i, (semiperimeter t - side t i)⁻¹ / ∑ j, (semiperimeter t - side t j)⁻¹ = 1 := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [← Finset.sum_div, div_self]
  rw [Fin.sum_univ_three, side0, side1, side2, ha, hb, hc, hs]
  ring_nf
  positivity

lemma centroid_vsub_zero : Finset.univ.centroid ℝ t.points -ᵥ t.points 0 =
    (1 / 3 : ℝ) • (t.points 1 -ᵥ t.points 0) + (1 / 3 : ℝ) • (t.points 2 -ᵥ t.points 0) := by
  rw [Finset.centroid_def, ac_vsub_base]
  · simp [Finset.centroidWeights_apply]
  · simp [Finset.centroidWeights_apply]

lemma nagel_vsub_zero : t.nagelPoint -ᵥ t.points 0 =
    ((semiperimeter t - side t 1) / semiperimeter t) • (t.points 1 -ᵥ t.points 0) +
      ((semiperimeter t - side t 2) / semiperimeter t) • (t.points 2 -ᵥ t.points 0) := by
  rw [Triangle.nagelPoint, ac_vsub_base _ _ (sum_nagel t)]
  simp

lemma incenter_vsub_zero : t.incenter -ᵥ t.points 0 =
    (side t 1 / (2 * semiperimeter t)) • (t.points 1 -ᵥ t.points 0) +
      (side t 2 / (2 * semiperimeter t)) • (t.points 2 -ᵥ t.points 0) := by
  rw [incenter_eq_affineCombination, ac_vsub_base _ _ (sum_in t)]
  simp

/-! ## The medial triangle -/

lemma medial_vsub (i j : Fin 3) : t.medial.points i -ᵥ t.medial.points j =
    (1 / 2 : ℝ) • (t.points j -ᵥ t.points i) := by
  rw [Simplex.medial_points, Simplex.medial_points,
    Simplex.faceOppositeCentroid_vsub_faceOppositeCentroid]
  norm_num

lemma medial_dist (i j : Fin 3) :
    dist (t.medial.points i) (t.medial.points j) = dist (t.points i) (t.points j) / 2 := by
  rw [dist_eq_norm_vsub V, medial_vsub, norm_smul, ← dist_eq_norm_vsub V, dist_comm]
  norm_num; ring

lemma medial_sideA : sideA t.medial = sideA t / 2 := medial_dist t 1 2
lemma medial_sideB : sideB t.medial = sideB t / 2 := medial_dist t 2 0
lemma medial_sideC : sideC t.medial = sideC t / 2 := medial_dist t 0 1

lemma medial_vsub_zero (i : Fin 3) : t.medial.points i -ᵥ t.points 0 =
    (1 / 2 : ℝ) • (Finset.univ.centroid ℝ t.points -ᵥ t.points i) +
      (Finset.univ.centroid ℝ t.points -ᵥ t.points 0) := by
  rw [Simplex.medial_points, Simplex.faceOppositeCentroid_eq_smul_vsub_vadd_point, vadd_vsub_assoc]
  norm_num

end NagelLine

/-! The main theorems take the triangle as an explicit argument and live outside the section
that declares `variable (t : Triangle ℝ P)`. -/

namespace NagelLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## Main theorems -/

/-- A1: each Gergonne cevian (vertex to incircle contact point on the opposite side) passes
through the Gergonne point. -/
theorem gergonnePoint_mem_cevian (t : Triangle ℝ P) :
    ∀ i, t.gergonnePoint ∈ line[ℝ, t.points i, t.touchpoint ∅ i] := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  have h0 : t.gergonnePoint ∈ line[ℝ, t.points 0, t.touchpoint ∅ 0] := by
    rw [touchpoint_empty_zero]
    refine cevian0 t _ (sum_gergonne t) _ ?_
    simp only [Fin.sum_univ_three, side0, side1, side2, ha, hb, hc, hs]
    have hS : (x + y + z - (y + z))⁻¹ + (x + y + z - (x + z))⁻¹ + (x + y + z - (x + y))⁻¹ ≠ 0 := by
      ring_nf; positivity
    have := hx.ne'; have := hy.ne'; have := hz.ne'
    ring_nf
    field_simp
    ring
  have h1 : t.gergonnePoint ∈ line[ℝ, t.points 1, t.touchpoint ∅ 1] := by
    rw [touchpoint_empty_one]
    refine cevian1 t _ (sum_gergonne t) _ ?_
    simp only [Fin.sum_univ_three, side0, side1, side2, ha, hb, hc, hs]
    have hS : (x + y + z - (y + z))⁻¹ + (x + y + z - (x + z))⁻¹ + (x + y + z - (x + y))⁻¹ ≠ 0 := by
      ring_nf; positivity
    have := hx.ne'; have := hy.ne'; have := hz.ne'
    ring_nf
    field_simp
    ring
  have h2 : t.gergonnePoint ∈ line[ℝ, t.points 2, t.touchpoint ∅ 2] := by
    rw [touchpoint_empty_two]
    refine cevian2 t _ (sum_gergonne t) _ ?_
    simp only [Fin.sum_univ_three, side0, side1, side2, ha, hb, hc, hs]
    have hS : (x + y + z - (y + z))⁻¹ + (x + y + z - (x + z))⁻¹ + (x + y + z - (x + y))⁻¹ ≠ 0 := by
      ring_nf; positivity
    have := hx.ne'; have := hy.ne'; have := hz.ne'
    ring_nf
    field_simp
    ring
  intro i
  fin_cases i
  exacts [h0, h1, h2]

/-- A1 corollary: the three Gergonne cevians are concurrent. -/
theorem gergonne_cevians_concurrent (t : Triangle ℝ P) :
    ∃ X : P, ∀ i, X ∈ line[ℝ, t.points i, t.touchpoint ∅ i] :=
  ⟨t.gergonnePoint, gergonnePoint_mem_cevian t⟩

/-- A2: each Nagel cevian (vertex `i` to the contact point of the excircle opposite `i` with the
side opposite `i`) passes through the Nagel point. -/
theorem nagelPoint_mem_cevian (t : Triangle ℝ P) :
    ∀ i, t.nagelPoint ∈ line[ℝ, t.points i, t.touchpoint {i} i] := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  have h0 : t.nagelPoint ∈ line[ℝ, t.points 0, t.touchpoint {0} 0] := by
    rw [touchpoint_singleton_zero]
    refine cevian0 t _ (sum_nagel t) _ ?_
    simp only [side1, side2, ha, hb, hc, hs]
    field_simp; ring
  have h1 : t.nagelPoint ∈ line[ℝ, t.points 1, t.touchpoint {1} 1] := by
    rw [touchpoint_singleton_one]
    refine cevian1 t _ (sum_nagel t) _ ?_
    simp only [side0, side2, ha, hb, hc, hs]
    field_simp; ring
  have h2 : t.nagelPoint ∈ line[ℝ, t.points 2, t.touchpoint {2} 2] := by
    rw [touchpoint_singleton_two]
    refine cevian2 t _ (sum_nagel t) _ ?_
    simp only [side0, side1, ha, hb, hc, hs]
    field_simp; ring
  intro i
  fin_cases i
  exacts [h0, h1, h2]

/-- A2 corollary: the three Nagel cevians are concurrent. -/
theorem nagel_cevians_concurrent (t : Triangle ℝ P) :
    ∃ X : P, ∀ i, X ∈ line[ℝ, t.points i, t.touchpoint {i} i] :=
  ⟨t.nagelPoint, nagelPoint_mem_cevian t⟩

/-- A3 (i): `N - G = 2 (G - I)`. -/
theorem nagelPoint_vsub_centroid (t : Triangle ℝ P) :
    t.nagelPoint -ᵥ Finset.univ.centroid ℝ t.points =
      (2 : ℝ) • (Finset.univ.centroid ℝ t.points -ᵥ t.incenter) := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [← vsub_sub_vsub_cancel_right t.nagelPoint _ (t.points 0),
    ← vsub_sub_vsub_cancel_right _ t.incenter (t.points 0), nagel_vsub_zero, incenter_vsub_zero,
    centroid_vsub_zero]
  simp only [side1, side2, hb, hc, hs]
  match_scalars <;> field_simp <;> ring

/-- A3 (i): the Nagel line — incentre, centroid and Nagel point are collinear. -/
theorem collinear_incenter_centroid_nagelPoint (t : Triangle ℝ P) :
    Collinear ℝ {t.incenter, Finset.univ.centroid ℝ t.points, t.nagelPoint} := by
  refine collinear_insert_of_mem_affineSpan_pair ?_
  have h : t.incenter = lineMap (Finset.univ.centroid ℝ t.points) t.nagelPoint (-(1 / 2 : ℝ)) := by
    rw [lineMap_apply, nagelPoint_vsub_centroid, smul_smul, eq_vadd_iff_vsub_eq,
      ← neg_vsub_eq_vsub_rev]
    norm_num
  rw [h]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- A3 (ii): the incentre of the medial triangle (the Spieker centre) is the midpoint of the
incentre and the Nagel point. -/
theorem medial_incenter_eq_midpoint (t : Triangle ℝ P) :
    t.medial.incenter = midpoint ℝ t.incenter t.nagelPoint := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  have hM : t.medial.incenter -ᵥ t.points 0 =
      (side t.medial 0 / (2 * semiperimeter t.medial)) • (t.medial.points 0 -ᵥ t.points 0) +
      (side t.medial 1 / (2 * semiperimeter t.medial)) • (t.medial.points 1 -ᵥ t.points 0) +
      (side t.medial 2 / (2 * semiperimeter t.medial)) • (t.medial.points 2 -ᵥ t.points 0) := by
    rw [incenter_eq_affineCombination t.medial, ac_vsub_base _ _ (sum_in t.medial)]
  have hG := centroid_vsub_zero t
  have e1 : Finset.univ.centroid ℝ t.points -ᵥ t.points 1 = (Finset.univ.centroid ℝ t.points -ᵥ
      t.points 0) - (t.points 1 -ᵥ t.points 0) := (vsub_sub_vsub_cancel_right _ _ _).symm
  have e2 : Finset.univ.centroid ℝ t.points -ᵥ t.points 2 = (Finset.univ.centroid ℝ t.points -ᵥ
      t.points 0) - (t.points 2 -ᵥ t.points 0) := (vsub_sub_vsub_cancel_right _ _ _).symm
  rw [← vsub_left_cancel_iff (p := t.points 0), midpoint_vsub, hM, medial_vsub_zero,
    medial_vsub_zero, medial_vsub_zero, e1, e2, hG, nagel_vsub_zero,
    incenter_vsub_zero]
  simp only [side0, side1, side2, semiperimeter, medial_sideA, medial_sideB, medial_sideC, ha, hb,
    hc]
  simp only [semiperimeter] at hs
  simp only [invOf_eq_inv]
  match_scalars <;> field_simp <;> ring

/-- A3 (ii): the Spieker centre lies on the Nagel line. -/
theorem collinear_spiekerCenter_incenter_nagelPoint (t : Triangle ℝ P) :
    Collinear ℝ {t.spiekerCenter, t.incenter, t.nagelPoint} := by
  refine collinear_insert_of_mem_affineSpan_pair ?_
  rw [Triangle.spiekerCenter, medial_incenter_eq_midpoint, midpoint]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

end NagelLine
