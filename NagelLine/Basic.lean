import Mathlib

open Affine EuclideanGeometry AffineMap
open scoped RealInnerProductSpace

namespace NagelLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- `a = dist B C`. -/
noncomputable def sideA (t : Triangle ℝ P) : ℝ := dist (t.points 1) (t.points 2)
/-- `b = dist C A`. -/
noncomputable def sideB (t : Triangle ℝ P) : ℝ := dist (t.points 2) (t.points 0)
/-- `c = dist A B`. -/
noncomputable def sideC (t : Triangle ℝ P) : ℝ := dist (t.points 0) (t.points 1)
/-- `s = (a + b + c) / 2`. -/
noncomputable def semiperimeter (t : Triangle ℝ P) : ℝ := (sideA t + sideB t + sideC t) / 2

/-- Twice the squared area as a symmetric polynomial in the side lengths (times 4). -/
noncomputable def heronPoly (x y z : ℝ) : ℝ :=
  (2 * x ^ 2 * y ^ 2 + 2 * y ^ 2 * z ^ 2 + 2 * z ^ 2 * x ^ 2 - x ^ 4 - y ^ 4 - z ^ 4) / 4

lemma inner_vsub_vsub_eq (X Y Z : P) :
    ⟪Y -ᵥ X, Z -ᵥ X⟫ = (dist X Y ^ 2 + dist X Z ^ 2 - dist Y Z ^ 2) / 2 := by
  rw [dist_comm X Y, dist_comm X Z, dist_eq_norm_vsub V Y X, dist_eq_norm_vsub V Z X,
    dist_eq_norm_vsub V Y Z, ← vsub_sub_vsub_cancel_right Y Z X, norm_sub_sq_real]
  ring

/-- Orthogonal projection onto a line through `Y`, `Z`, given the parameter explicitly. -/
lemma proj_eq_lineMap {S : AffineSubspace ℝ P} [Nonempty S] [S.direction.HasOrthogonalProjection]
    {Y Z : P} (hS : S = line[ℝ, Y, Z]) (Q : P) (r : ℝ)
    (h : ⟪Q -ᵥ Y, Z -ᵥ Y⟫ = r * dist Y Z ^ 2) :
    (orthogonalProjection S Q : P) = lineMap Y Z r := by
  rw [coe_orthogonalProjection_eq_iff_mem]
  subst hS
  refine ⟨AffineMap.lineMap_mem_affineSpan_pair _ _ _, ?_⟩
  rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right,
    lineMap_apply, vsub_vadd_eq_vsub_sub, ← neg_vsub_eq_vsub_rev Z Y, inner_neg_left,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, ← dist_eq_norm_vsub V Z Y,
    real_inner_comm, h, dist_comm]
  ring

lemma height_sq_mul {X Y Z : P} {x y z r : ℝ} (hx : dist Y Z = x) (hy : dist Z X = y)
    (hz : dist X Y = z) (h : ⟪X -ᵥ Y, Z -ᵥ Y⟫ = r * x ^ 2) :
    (dist X (lineMap Y Z r) * x) ^ 2 = heronPoly x y z := by
  have h2 := inner_vsub_vsub_eq Y X Z
  rw [h, dist_comm Y X, hz, hx, dist_comm X Z, hy] at h2
  have e : X -ᵥ lineMap Y Z r = (X -ᵥ Y) - r • (Z -ᵥ Y) := by
    rw [lineMap_apply, vsub_vadd_eq_vsub_sub]
  have n1 : ‖X -ᵥ Y‖ = z := by rw [← dist_eq_norm_vsub, hz]
  have n2 : ‖Z -ᵥ Y‖ = x := by rw [← dist_eq_norm_vsub, dist_comm, hx]
  rw [mul_pow, dist_eq_norm_vsub V, e, norm_sub_sq_real, norm_smul, inner_smul_right, h, n1, n2,
    Real.norm_eq_abs, mul_pow, sq_abs, heronPoly]
  linear_combination (-(r * x ^ 2 + (z ^ 2 + x ^ 2 - y ^ 2) / 2)) * h2


variable (t : Triangle ℝ P)

lemma range_face0 : Set.range (t.faceOpposite 0).points = {t.points 1, t.points 2} := by
  rw [Simplex.range_faceOpposite_points]
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    fin_cases j <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨1, by decide, rfl⟩
    · exact ⟨2, by decide, rfl⟩

lemma range_face1 : Set.range (t.faceOpposite 1).points = {t.points 2, t.points 0} := by
  rw [Simplex.range_faceOpposite_points]
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    fin_cases j <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨2, by decide, rfl⟩
    · exact ⟨0, by decide, rfl⟩

lemma range_face2 : Set.range (t.faceOpposite 2).points = {t.points 0, t.points 1} := by
  rw [Simplex.range_faceOpposite_points]
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    fin_cases j <;> simp_all
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩

lemma projSpan0 (Q : P) (r : ℝ)
    (h : ⟪Q -ᵥ t.points 1, t.points 2 -ᵥ t.points 1⟫ = r * dist (t.points 1) (t.points 2) ^ 2) :
    ((t.faceOpposite 0).orthogonalProjectionSpan Q : P) = lineMap (t.points 1) (t.points 2) r :=
  proj_eq_lineMap (by rw [range_face0]) Q r h

lemma projSpan1 (Q : P) (r : ℝ)
    (h : ⟪Q -ᵥ t.points 2, t.points 0 -ᵥ t.points 2⟫ = r * dist (t.points 2) (t.points 0) ^ 2) :
    ((t.faceOpposite 1).orthogonalProjectionSpan Q : P) = lineMap (t.points 2) (t.points 0) r :=
  proj_eq_lineMap (by rw [range_face1]) Q r h

lemma projSpan2 (Q : P) (r : ℝ)
    (h : ⟪Q -ᵥ t.points 0, t.points 1 -ᵥ t.points 0⟫ = r * dist (t.points 0) (t.points 1) ^ 2) :
    ((t.faceOpposite 2).orthogonalProjectionSpan Q : P) = lineMap (t.points 0) (t.points 1) r :=
  proj_eq_lineMap (by rw [range_face2]) Q r h

lemma sideA_pos : 0 < sideA t :=
  dist_pos.2 fun h ↦ by simpa using t.independent.injective h
lemma sideB_pos : 0 < sideB t :=
  dist_pos.2 fun h ↦ by simpa using t.independent.injective h
lemma sideC_pos : 0 < sideC t :=
  dist_pos.2 fun h ↦ by simpa using t.independent.injective h

lemma height0_sq : (t.height 0 * sideA t) ^ 2 = heronPoly (sideA t) (sideB t) (sideC t) := by
  have ha := (sideA_pos t).ne'
  have hp : t.altitudeFoot 0 = lineMap (t.points 1) (t.points 2)
      (⟪t.points 0 -ᵥ t.points 1, t.points 2 -ᵥ t.points 1⟫ / sideA t ^ 2) :=
    projSpan0 t _ _ (by rw [← sideA]; field_simp)
  rw [Simplex.height, hp]
  exact height_sq_mul rfl rfl rfl (by field_simp)

lemma height1_sq : (t.height 1 * sideB t) ^ 2 = heronPoly (sideA t) (sideB t) (sideC t) := by
  have ha := (sideB_pos t).ne'
  have hp : t.altitudeFoot 1 = lineMap (t.points 2) (t.points 0)
      (⟪t.points 1 -ᵥ t.points 2, t.points 0 -ᵥ t.points 2⟫ / sideB t ^ 2) :=
    projSpan1 t _ _ (by rw [← sideB]; field_simp)
  rw [Simplex.height, hp]
  exact (height_sq_mul (x := sideB t) (y := sideC t) (z := sideA t) rfl rfl rfl (by field_simp)).trans
    (by simp only [heronPoly]; ring)

lemma height2_sq : (t.height 2 * sideC t) ^ 2 = heronPoly (sideA t) (sideB t) (sideC t) := by
  have ha := (sideC_pos t).ne'
  have hp : t.altitudeFoot 2 = lineMap (t.points 0) (t.points 1)
      (⟪t.points 2 -ᵥ t.points 0, t.points 1 -ᵥ t.points 0⟫ / sideC t ^ 2) :=
    projSpan2 t _ _ (by rw [← sideC]; field_simp)
  rw [Simplex.height, hp]
  exact (height_sq_mul (x := sideC t) (y := sideA t) (z := sideB t) rfl rfl rfl (by field_simp)).trans
    (by simp only [heronPoly]; ring)

/-- Twice the area: `height · side`, independent of the side. -/
noncomputable def dblArea : ℝ := t.height 0 * sideA t

lemma dblArea_pos : 0 < dblArea t := mul_pos (t.height_pos 0) (sideA_pos t)

lemma height0_eq : t.height 0 = dblArea t / sideA t := by
  rw [dblArea]; field_simp [(sideA_pos t).ne']

lemma height1_eq : t.height 1 = dblArea t / sideB t := by
  have h : t.height 1 * sideB t = dblArea t := by
    rw [← sq_eq_sq₀ (mul_pos (t.height_pos 1) (sideB_pos t)).le (dblArea_pos t).le, height1_sq,
      dblArea, height0_sq]
  rw [← h]; field_simp [(sideB_pos t).ne']

lemma height2_eq : t.height 2 = dblArea t / sideC t := by
  have h : t.height 2 * sideC t = dblArea t := by
    rw [← sq_eq_sq₀ (mul_pos (t.height_pos 2) (sideC_pos t)).le (dblArea_pos t).le, height2_sq,
      dblArea, height0_sq]
  rw [← h]; field_simp [(sideC_pos t).ne']

lemma heron_factor :
    heronPoly (sideA t) (sideB t) (sideC t) = 4 * semiperimeter t * (semiperimeter t - sideA t) *
      (semiperimeter t - sideB t) * (semiperimeter t - sideC t) := by
  simp only [heronPoly, semiperimeter]; ring

lemma prod_pos : 0 < semiperimeter t * ((semiperimeter t - sideA t) *
      ((semiperimeter t - sideB t) * (semiperimeter t - sideC t))) := by
  have h := dblArea_pos t
  have h2 : 0 < dblArea t ^ 2 := by positivity
  rw [dblArea, height0_sq, heron_factor] at h2
  linarith

lemma semiperimeter_pos : 0 < semiperimeter t := by
  have := sideA_pos t; have := sideB_pos t; have := sideC_pos t
  rw [semiperimeter]; linarith

lemma sub_pos_aux {x y z : ℝ} (hxy : 0 < x + y) (hxz : 0 < x + z) (_hyz : 0 < y + z)
    (h : 0 < x * (y * z)) : 0 < x := by
  by_contra hx
  push Not at hx
  have : x * (y * z) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hx (mul_nonneg (by linarith) (by linarith))
  linarith

lemma triple_pos : 0 < (semiperimeter t - sideA t) *
      ((semiperimeter t - sideB t) * (semiperimeter t - sideC t)) :=
  pos_of_mul_pos_right (prod_pos t) (semiperimeter_pos t).le

lemma s_sub_a_pos : 0 < semiperimeter t - sideA t := by
  have := sideA_pos t; have := sideB_pos t; have := sideC_pos t
  refine sub_pos_aux (y := semiperimeter t - sideB t) (z := semiperimeter t - sideC t)
    ?_ ?_ ?_ (triple_pos t) <;> rw [semiperimeter] <;> linarith

lemma s_sub_b_pos : 0 < semiperimeter t - sideB t := by
  have := sideA_pos t; have := sideB_pos t; have := sideC_pos t
  refine sub_pos_aux (y := semiperimeter t - sideA t) (z := semiperimeter t - sideC t)
    ?_ ?_ ?_ (by have := triple_pos t; linarith [this, show (semiperimeter t - sideB t) *
      ((semiperimeter t - sideA t) * (semiperimeter t - sideC t)) = (semiperimeter t - sideA t) *
      ((semiperimeter t - sideB t) * (semiperimeter t - sideC t)) by ring]) <;>
    rw [semiperimeter] <;> linarith

lemma s_sub_c_pos : 0 < semiperimeter t - sideC t := by
  have := sideA_pos t; have := sideB_pos t; have := sideC_pos t
  refine sub_pos_aux (y := semiperimeter t - sideA t) (z := semiperimeter t - sideB t)
    ?_ ?_ ?_ (by have := triple_pos t; linarith [this, show (semiperimeter t - sideC t) *
      ((semiperimeter t - sideA t) * (semiperimeter t - sideB t)) = (semiperimeter t - sideA t) *
      ((semiperimeter t - sideB t) * (semiperimeter t - sideC t)) by ring]) <;>
    rw [semiperimeter] <;> linarith

/-- Side lengths indexed by the opposite vertex. -/
noncomputable def side (i : Fin 3) : ℝ := ![sideA t, sideB t, sideC t] i

lemma height_eq (i : Fin 3) : t.height i = dblArea t / side t i := by
  fin_cases i
  · exact height0_eq t
  · exact height1_eq t
  · exact height2_eq t

lemma incenter_weights :
    t.excenterWeights ∅ = fun i ↦ side t i / (2 * semiperimeter t) := by
  have hs := semiperimeter_pos t
  have hK := (dblArea_pos t).ne'
  have := sideA_pos t; have := sideB_pos t; have := sideC_pos t
  funext i
  simp only [Simplex.excenterWeights, Pi.smul_apply, Simplex.excenterWeightsUnnorm_empty_apply,
    height_eq, smul_eq_mul]
  rw [Fin.sum_univ_three]
  have e : 2 * semiperimeter t = side t 0 + side t 1 + side t 2 := by
    simp [side, semiperimeter]; ring
  rw [e]
  have h0 : side t 0 ≠ 0 := by simp [side]; positivity
  have h1 : side t 1 ≠ 0 := by simp [side]; positivity
  have h2 : side t 2 ≠ 0 := by simp [side]; positivity
  have h3 : side t 0 + side t 1 + side t 2 ≠ 0 := by simp [side]; positivity
  have hi : side t i ≠ 0 := by fin_cases i <;> assumption
  field_simp

lemma excenter_weights (i : Fin 3) : t.excenterWeights {i} =
    fun j ↦ (if j = i then -1 else 1) * side t j / (2 * (semiperimeter t - side t i)) := by
  have hK := (dblArea_pos t).ne'
  have := sideA_pos t; have := sideB_pos t; have := sideC_pos t
  have := s_sub_a_pos t; have := s_sub_b_pos t; have := s_sub_c_pos t
  have h0 : side t 0 ≠ 0 := by simp [side]; positivity
  have h1 : side t 1 ≠ 0 := by simp [side]; positivity
  have h2 : side t 2 ≠ 0 := by simp [side]; positivity
  funext j
  simp only [Simplex.excenterWeights, Pi.smul_apply, Simplex.excenterWeightsUnnorm,
    Finset.mem_singleton, height_eq, smul_eq_mul]
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
  · simp only [side, semiperimeter] at *
    simp
    field_simp
    ring


end NagelLine

namespace Affine.Triangle

open NagelLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The Nagel point: weights `(s-a)/s, (s-b)/s, (s-c)/s` on `A, B, C`. -/
noncomputable def nagelPoint (t : Triangle ℝ P) : P :=
  Finset.univ.affineCombination ℝ t.points fun i ↦ (semiperimeter t - side t i) / semiperimeter t

/-- The Gergonne point: weights proportional to `1/(s-a), 1/(s-b), 1/(s-c)`, normalised. -/
noncomputable def gergonnePoint (t : Triangle ℝ P) : P :=
  Finset.univ.affineCombination ℝ t.points fun i ↦
    (semiperimeter t - side t i)⁻¹ / ∑ j, (semiperimeter t - side t j)⁻¹

/-- The Spieker centre: the incentre of the medial triangle. -/
noncomputable def spiekerCenter (t : Triangle ℝ P) : P := t.medial.incenter

end Affine.Triangle

namespace NagelLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

end NagelLine
