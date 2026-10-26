import NagelLine.Main

/-!
# Extensions: de Longchamps point, anticomplementary triangle, medial Nagel point, Spieker centre

* C1: the de Longchamps point `L` (reflection of the orthocentre `H` in the circumcentre `O`) lies
  on the Euler line, `O` is the midpoint of `H` and `L`, and `L` is the orthocentre of the
  anticomplementary triangle.
* C2: the Nagel point of the medial triangle is the incentre; the incircle and excircle contact
  points on each side are symmetric about the midpoint of that side.
* C3: the Nagel point is the incentre of the anticomplementary triangle.
* C4: the Spieker centre has equal power with respect to the three excircles.
-/

open Affine EuclideanGeometry AffineMap
open scoped RealInnerProductSpace

namespace Affine.Triangle

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The de Longchamps point: the reflection of the orthocentre in the circumcentre. -/
noncomputable def deLongchampsPoint (t : Triangle ℝ P) : P :=
  (2 : ℝ) • (t.circumcenter -ᵥ t.orthocenter) +ᵥ t.orthocenter

/-- The anticomplementary triangle: the image of `t` under the homothety with centre the centroid
and ratio `-2`. Its vertices are `B + C - A`, `C + A - B`, `A + B - C`
(see `anticomplementary_points_zero` etc.). -/
noncomputable def anticomplementary (t : Triangle ℝ P) : Triangle ℝ P :=
  t.map (homothety (Finset.univ.centroid ℝ t.points) (-2 : ℝ))
    (homothety_injective _ (by norm_num))

end Affine.Triangle

namespace NagelLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

lemma norm_comb_sq (u v : V) (α β : ℝ) :
    ‖α • u + β • v‖ ^ 2 = α ^ 2 * ‖u‖ ^ 2 + β ^ 2 * ‖v‖ ^ 2 + 2 * α * β * ⟪u, v⟫ := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

lemma midpoint_lineMap_lineMap (X Y : P) (r₁ r₂ : ℝ) (h : r₁ + r₂ = 1) :
    midpoint ℝ (lineMap X Y r₁) (lineMap X Y r₂) = midpoint ℝ X Y := by
  rw [← vsub_left_cancel_iff (p := X), midpoint_vsub, midpoint_vsub, lineMap_vsub_left,
    lineMap_vsub_left, vsub_self, smul_zero, zero_add, smul_smul, smul_smul, ← add_smul, ← mul_add,
    h, mul_one]

variable (t : Triangle ℝ P)

/-! ## Bridges: anticomplementary triangle -/

theorem anticomplementary_points (i : Fin 3) : t.anticomplementary.points i =
    (-2 : ℝ) • (t.points i -ᵥ Finset.univ.centroid ℝ t.points) +ᵥ
      Finset.univ.centroid ℝ t.points := by
  simp only [Triangle.anticomplementary, Simplex.map_points, Function.comp_apply, homothety_apply]

/-- First vertex of the anticomplementary triangle: `B + C - A`. -/
theorem anticomplementary_points_zero :
    t.anticomplementary.points 0 = (t.points 1 -ᵥ t.points 0) +ᵥ t.points 2 := by
  rw [anticomplementary_points, ← vsub_left_cancel_iff (p := t.points 0), vadd_vsub_assoc,
    vadd_vsub_assoc, ← neg_vsub_eq_vsub_rev (Finset.univ.centroid ℝ t.points) (t.points 0),
    centroid_vsub_zero]
  module

/-- Second vertex: `C + A - B`. -/
theorem anticomplementary_points_one :
    t.anticomplementary.points 1 = (t.points 2 -ᵥ t.points 1) +ᵥ t.points 0 := by
  rw [anticomplementary_points, ← vsub_left_cancel_iff (p := t.points 0), vadd_vsub_assoc,
    vadd_vsub, ← vsub_sub_vsub_cancel_right (t.points 1) _ (t.points 0),
    ← vsub_sub_vsub_cancel_right (t.points 2) (t.points 1) (t.points 0), centroid_vsub_zero]
  module

/-- Third vertex: `A + B - C`. -/
theorem anticomplementary_points_two :
    t.anticomplementary.points 2 = (t.points 0 -ᵥ t.points 2) +ᵥ t.points 1 := by
  rw [anticomplementary_points, ← vsub_left_cancel_iff (p := t.points 0), vadd_vsub_assoc,
    vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right (t.points 2) _ (t.points 0),
    ← neg_vsub_eq_vsub_rev (t.points 2) (t.points 0), centroid_vsub_zero]
  module

theorem centroid_anticomplementary :
    Finset.univ.centroid ℝ t.anticomplementary.points = Finset.univ.centroid ℝ t.points := by
  have h := Simplex.centroid_map t (homothety (Finset.univ.centroid ℝ t.points) (-2 : ℝ))
    (homothety_injective _ (by norm_num))
  exact h.trans (homothety_apply_same _ _)

/-- The medial triangle of the anticomplementary triangle is the original triangle. -/
theorem anticomplementary_medial : t.anticomplementary.medial = t := by
  ext i
  have hc : t.anticomplementary.centroid = Finset.univ.centroid ℝ t.points :=
    centroid_anticomplementary t
  rw [Simplex.medial_points, Simplex.faceOppositeCentroid_eq_smul_vsub_vadd_point, hc,
    anticomplementary_points, vsub_vadd_eq_vsub_sub, vsub_self, zero_sub, smul_neg, smul_smul,
    ← neg_smul]
  norm_num

/-! ## Bridges: Euler line -/

theorem orthocenter_vsub_circumcenter : t.orthocenter -ᵥ t.circumcenter =
    (3 : ℝ) • (Finset.univ.centroid ℝ t.points -ᵥ t.circumcenter) := by
  rw [Triangle.orthocenter_eq_smul_vsub_vadd_circumcenter, vadd_vsub]

theorem deLongchampsPoint_vsub_circumcenter : t.deLongchampsPoint -ᵥ t.circumcenter =
    (3 : ℝ) • (t.circumcenter -ᵥ Finset.univ.centroid ℝ t.points) := by
  rw [Triangle.deLongchampsPoint, vadd_vsub_assoc,
    ← neg_vsub_eq_vsub_rev t.orthocenter t.circumcenter, orthocenter_vsub_circumcenter,
    ← neg_vsub_eq_vsub_rev (Finset.univ.centroid ℝ t.points) t.circumcenter]
  module

/-- The circumcentre of the anticomplementary triangle is the orthocentre. -/
theorem anticomplementary_circumcenter :
    t.anticomplementary.circumcenter = t.orthocenter := by
  set G := Finset.univ.centroid ℝ t.points
  have hspan : affineSpan ℝ (Set.range t.anticomplementary.points) =
      (affineSpan ℝ (Set.range t.points)).map (homothety G (-2 : ℝ)) := by
    rw [AffineSubspace.map_span, Triangle.anticomplementary, Simplex.map_points, Set.range_comp]
  have hv (i : Fin 3) : t.anticomplementary.points i -ᵥ t.orthocenter =
      (-2 : ℝ) • (t.points i -ᵥ t.circumcenter) := by
    rw [anticomplementary_points, ← vsub_sub_vsub_cancel_right _ t.orthocenter t.circumcenter,
      orthocenter_vsub_circumcenter, vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right (t.points i) G
      t.circumcenter]
    module
  symm
  refine t.anticomplementary.eq_circumcenter_of_dist_eq (r := 2 * t.circumradius) ?_ ?_
  · rw [hspan]
    refine AffineSubspace.mem_map.2 ⟨homothety G (-1 / 2 : ℝ) t.orthocenter, ?_, ?_⟩
    · rw [homothety_eq_lineMap]
      exact AffineMap.lineMap_mem _
        (centroid_mem_affineSpan_of_card_ne_zero ℝ t.points (by simp))
        (Triangle.orthocenter_mem_affineSpan t)
    · rw [homothety_apply, homothety_apply, vadd_vsub, smul_smul]
      norm_num
  · intro i
    rw [dist_eq_norm_vsub V, hv, norm_smul, ← dist_eq_norm_vsub V,
      Simplex.dist_circumcenter_eq_circumradius]
    norm_num

/-! ## Bridges: excircles -/

lemma dist_sq_of_vsub {X Y : P} {x1 x2 y1 y2 : ℝ}
    (hX : X -ᵥ t.points 0 = x1 • (t.points 1 -ᵥ t.points 0) + x2 • (t.points 2 -ᵥ t.points 0))
    (hY : Y -ᵥ t.points 0 = y1 • (t.points 1 -ᵥ t.points 0) + y2 • (t.points 2 -ᵥ t.points 0)) :
    dist X Y ^ 2 = (x1 - y1) ^ 2 * sideC t ^ 2 + (x2 - y2) ^ 2 * sideB t ^ 2 +
      (x1 - y1) * (x2 - y2) * (sideB t ^ 2 + sideC t ^ 2 - sideA t ^ 2) := by
  have hb := inner_vsub_vsub_eq (t.points 0) (t.points 1) (t.points 2)
  rw [dist_eq_norm_vsub V, ← vsub_sub_vsub_cancel_right X Y (t.points 0), hX, hY]
  have e : (x1 • (t.points 1 -ᵥ t.points 0) + x2 • (t.points 2 -ᵥ t.points 0)) -
      (y1 • (t.points 1 -ᵥ t.points 0) + y2 • (t.points 2 -ᵥ t.points 0)) =
      (x1 - y1) • (t.points 1 -ᵥ t.points 0) + (x2 - y2) • (t.points 2 -ᵥ t.points 0) := by
    module
  rw [e, norm_comb_sq, hb, ← dist_eq_norm_vsub V (t.points 1), ← dist_eq_norm_vsub V (t.points 2),
    d10, d20, d01, d02, d12]
  ring

theorem sum_excenterWeightsUnnorm_singleton (i : Fin 3) :
    ∑ j, t.excenterWeightsUnnorm {i} j = 2 * (semiperimeter t - side t i) / dblArea t := by
  have hK := (dblArea_pos t).ne'
  have := sideA_pos t; have := sideB_pos t; have := sideC_pos t
  simp only [Simplex.excenterWeightsUnnorm, Finset.mem_singleton, height_eq]
  rw [Fin.sum_univ_three]
  fin_cases i <;>
  · simp only [side, semiperimeter]
    simp
    field_simp
    ring

theorem exradius_singleton_sq (i : Fin 3) : t.exradius {i} ^ 2 =
    4 * semiperimeter t * (semiperimeter t - sideA t) * (semiperimeter t - sideB t) *
      (semiperimeter t - sideC t) / (2 * (semiperimeter t - side t i)) ^ 2 := by
  have hK2 : dblArea t ^ 2 = 4 * semiperimeter t * (semiperimeter t - sideA t) *
      (semiperimeter t - sideB t) * (semiperimeter t - sideC t) := by
    rw [dblArea, height0_sq, heron_factor]
  rw [Simplex.exradius_eq_abs_inv_sum, sq_abs, sum_excenterWeightsUnnorm_singleton, inv_div,
    div_pow, hK2]

theorem excenter_singleton_vsub_zero (i : Fin 3) : t.excenter {i} -ᵥ t.points 0 =
    ((if (1 : Fin 3) = i then -1 else 1) * side t 1 / (2 * (semiperimeter t - side t i))) •
        (t.points 1 -ᵥ t.points 0) +
      ((if (2 : Fin 3) = i then -1 else 1) * side t 2 / (2 * (semiperimeter t - side t i))) •
        (t.points 2 -ᵥ t.points 0) := by
  rw [excenter_singleton_eq_affineCombination, ac_vsub_base _ _ (sum_ex t i)]
  simp only [vsub_self, smul_zero, zero_add]

theorem spiekerCenter_vsub_zero : t.spiekerCenter -ᵥ t.points 0 =
    ((side t 1 / (2 * semiperimeter t) + (semiperimeter t - side t 1) / semiperimeter t) / 2) •
        (t.points 1 -ᵥ t.points 0) +
      ((side t 2 / (2 * semiperimeter t) + (semiperimeter t - side t 2) / semiperimeter t) / 2) •
        (t.points 2 -ᵥ t.points 0) := by
  rw [Triangle.spiekerCenter, medial_incenter_eq_midpoint, midpoint_vsub, incenter_vsub_zero,
    nagel_vsub_zero]
  simp only [invOf_eq_inv]
  module

/-- The power of the Spieker centre with respect to each excircle is `(s² + r²) / 4`, where
`r² = (s - a)(s - b)(s - c) / s` is the squared inradius. -/
theorem spiekerCenter_power_exsphere_eq (i : Fin 3) :
    dist t.spiekerCenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 =
      (semiperimeter t ^ 2 + (semiperimeter t - sideA t) * (semiperimeter t - sideB t) *
        (semiperimeter t - sideC t) / semiperimeter t) / 4 := by
  have hS := spiekerCenter_vsub_zero t
  rw [Simplex.exsphere_center, dist_sq_of_vsub t hS (excenter_singleton_vsub_zero t i),
    exradius_singleton_sq]
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  have := hx.ne'; have := hy.ne'; have := hz.ne'
  fin_cases i <;>
  · simp only [side, semiperimeter] at hs ⊢
    simp
    rw [ha, hb, hc]
    ring_nf
    field_simp
    ring

end NagelLine

namespace NagelLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## C1: the de Longchamps point -/

/-- C1: the circumcentre is the midpoint of the orthocentre and the de Longchamps point. -/
theorem midpoint_orthocenter_deLongchampsPoint (t : Triangle ℝ P) :
    midpoint ℝ t.orthocenter t.deLongchampsPoint = t.circumcenter := by
  rw [← vsub_left_cancel_iff (p := t.circumcenter), midpoint_vsub, vsub_self,
    deLongchampsPoint_vsub_circumcenter, orthocenter_vsub_circumcenter,
    ← neg_vsub_eq_vsub_rev (Finset.univ.centroid ℝ t.points) t.circumcenter]
  simp only [invOf_eq_inv]
  module

/-- C1: `L`, `O`, `H` are collinear. -/
theorem collinear_deLongchampsPoint_circumcenter_orthocenter (t : Triangle ℝ P) :
    Collinear ℝ {t.deLongchampsPoint, t.circumcenter, t.orthocenter} := by
  refine collinear_insert_of_mem_affineSpan_pair ?_
  have h : t.deLongchampsPoint = lineMap t.circumcenter t.orthocenter (-1 : ℝ) := by
    rw [lineMap_apply, eq_vadd_iff_vsub_eq, deLongchampsPoint_vsub_circumcenter,
      orthocenter_vsub_circumcenter,
      ← neg_vsub_eq_vsub_rev (Finset.univ.centroid ℝ t.points) t.circumcenter]
    module
  rw [h]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- C1: the de Longchamps point lies on the Euler line `G O`. -/
theorem collinear_centroid_circumcenter_deLongchampsPoint (t : Triangle ℝ P) :
    Collinear ℝ {Finset.univ.centroid ℝ t.points, t.circumcenter, t.deLongchampsPoint} := by
  refine collinear_insert_of_mem_affineSpan_pair ?_
  have h : Finset.univ.centroid ℝ t.points =
      lineMap t.circumcenter t.deLongchampsPoint (-(1 / 3) : ℝ) := by
    rw [lineMap_apply, eq_vadd_iff_vsub_eq, deLongchampsPoint_vsub_circumcenter,
      ← neg_vsub_eq_vsub_rev (Finset.univ.centroid ℝ t.points) t.circumcenter]
    module
  rw [h]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- C1: the de Longchamps point is the orthocentre of the anticomplementary triangle. -/
theorem anticomplementary_orthocenter (t : Triangle ℝ P) :
    t.anticomplementary.orthocenter = t.deLongchampsPoint := by
  rw [Triangle.orthocenter_eq_smul_vsub_vadd_circumcenter, centroid_anticomplementary,
    anticomplementary_circumcenter, ← vsub_left_cancel_iff (p := t.circumcenter), vadd_vsub_assoc,
    deLongchampsPoint_vsub_circumcenter,
    ← vsub_sub_vsub_cancel_right (Finset.univ.centroid ℝ t.points) t.orthocenter t.circumcenter,
    orthocenter_vsub_circumcenter,
    ← neg_vsub_eq_vsub_rev (Finset.univ.centroid ℝ t.points) t.circumcenter]
  module

/-! ## C2: the medial triangle and isotomic contact points -/

/-- C2: the Nagel point of the medial triangle is the incentre. -/
theorem medial_nagelPoint (t : Triangle ℝ P) : Triangle.nagelPoint t.medial = t.incenter := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  have hM : Triangle.nagelPoint t.medial -ᵥ t.points 0 =
      ((semiperimeter t.medial - side t.medial 0) / semiperimeter t.medial) •
        (t.medial.points 0 -ᵥ t.points 0) +
      ((semiperimeter t.medial - side t.medial 1) / semiperimeter t.medial) •
        (t.medial.points 1 -ᵥ t.points 0) +
      ((semiperimeter t.medial - side t.medial 2) / semiperimeter t.medial) •
        (t.medial.points 2 -ᵥ t.points 0) := by
    rw [Triangle.nagelPoint, ac_vsub_base _ _ (sum_nagel t.medial)]
  have hG := centroid_vsub_zero t
  have e1 : Finset.univ.centroid ℝ t.points -ᵥ t.points 1 = (Finset.univ.centroid ℝ t.points -ᵥ
      t.points 0) - (t.points 1 -ᵥ t.points 0) := (vsub_sub_vsub_cancel_right _ _ _).symm
  have e2 : Finset.univ.centroid ℝ t.points -ᵥ t.points 2 = (Finset.univ.centroid ℝ t.points -ᵥ
      t.points 0) - (t.points 2 -ᵥ t.points 0) := (vsub_sub_vsub_cancel_right _ _ _).symm
  rw [← vsub_left_cancel_iff (p := t.points 0), hM, medial_vsub_zero, medial_vsub_zero,
    medial_vsub_zero, e1, e2, hG, incenter_vsub_zero]
  simp only [side0, side1, side2, semiperimeter, medial_sideA, medial_sideB, medial_sideC, ha, hb,
    hc]
  simp only [semiperimeter] at hs
  match_scalars <;> field_simp <;> ring

/-- C2: incircle and `A`-excircle contact points on `BC` are symmetric about the midpoint of `BC`. -/
theorem midpoint_touchpoint_zero (t : Triangle ℝ P) :
    midpoint ℝ (t.touchpoint ∅ 0) (t.touchpoint {0} 0) = midpoint ℝ (t.points 1) (t.points 2) := by
  rw [touchpoint_empty_zero, touchpoint_singleton_zero]
  refine midpoint_lineMap_lineMap _ _ _ _ ?_
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [ha, hb, hc, hs]
  have : y + z ≠ 0 := by positivity
  field_simp
  ring

/-- C2: the same on `CA`. -/
theorem midpoint_touchpoint_one (t : Triangle ℝ P) :
    midpoint ℝ (t.touchpoint ∅ 1) (t.touchpoint {1} 1) = midpoint ℝ (t.points 2) (t.points 0) := by
  rw [touchpoint_empty_one, touchpoint_singleton_one]
  refine midpoint_lineMap_lineMap _ _ _ _ ?_
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [ha, hb, hc, hs]
  have : x + z ≠ 0 := by positivity
  field_simp
  ring

/-- C2: the same on `AB`. -/
theorem midpoint_touchpoint_two (t : Triangle ℝ P) :
    midpoint ℝ (t.touchpoint ∅ 2) (t.touchpoint {2} 2) = midpoint ℝ (t.points 0) (t.points 1) := by
  rw [touchpoint_empty_two, touchpoint_singleton_two]
  refine midpoint_lineMap_lineMap _ _ _ _ ?_
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  rw [ha, hb, hc, hs]
  have : x + y ≠ 0 := by positivity
  field_simp
  ring

/-! ## C3: the Nagel point and the anticomplementary triangle -/

/-- C3: the Nagel point is the incentre of the anticomplementary triangle. -/
theorem nagelPoint_eq_anticomplementary_incenter (t : Triangle ℝ P) :
    t.nagelPoint = t.anticomplementary.incenter := by
  obtain ⟨x, y, z, hx, hy, hz, ha, hb, hc, hs⟩ := ravi t
  have hA : sideA t.anticomplementary = 2 * sideA t := by
    have h := medial_sideA t.anticomplementary
    rw [anticomplementary_medial] at h; linarith
  have hB : sideB t.anticomplementary = 2 * sideB t := by
    have h := medial_sideB t.anticomplementary
    rw [anticomplementary_medial] at h; linarith
  have hC : sideC t.anticomplementary = 2 * sideC t := by
    have h := medial_sideC t.anticomplementary
    rw [anticomplementary_medial] at h; linarith
  rw [← vsub_left_cancel_iff (p := t.points 0), nagel_vsub_zero,
    incenter_eq_affineCombination t.anticomplementary,
    ac_vsub_base _ _ (sum_in t.anticomplementary), anticomplementary_points_zero,
    anticomplementary_points_one, anticomplementary_points_two, vadd_vsub_assoc, vadd_vsub,
    vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right (t.points 2) (t.points 1) (t.points 0),
    ← neg_vsub_eq_vsub_rev (t.points 2) (t.points 0)]
  simp only [side0, side1, side2, semiperimeter, hA, hB, hC, ha, hb, hc]
  simp only [semiperimeter] at hs
  match_scalars <;> field_simp <;> ring

/-! ## C4: the Spieker centre is the radical centre of the excircles -/

/-- C4: the Spieker centre has the same power with respect to all three excircles. -/
theorem spiekerCenter_power_exsphere (t : Triangle ℝ P) (i j : Fin 3) :
    dist t.spiekerCenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 =
      dist t.spiekerCenter (t.exsphere {j}).center ^ 2 - t.exradius {j} ^ 2 := by
  rw [spiekerCenter_power_exsphere_eq, spiekerCenter_power_exsphere_eq]

end NagelLine
