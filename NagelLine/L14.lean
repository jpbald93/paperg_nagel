import NagelLine.Extensions

/-!
# Layer 14: Mathlib-only restatements and witnesses for the Nagel line family

Every `l14_*` theorem below has a statement mentioning only Mathlib notions: Mathlib's
`incenter`, `excenter`, `touchpoint`, `exsphere`, `exradius`, `medial`, `circumcenter`,
`orthocenter` and `Finset.centroid`, with the library's `nagelPoint`, `gergonnePoint`,
`spiekerCenter`, `deLongchampsPoint` and `anticomplementary` unfolded: the Nagel and Gergonne
points are explicit `Finset.univ.affineCombination`s in the side lengths `a = dist B C`,
`b = dist C A`, `c = dist A B` and `s = (a + b + c) / 2`; the Spieker centre is `t.medial.incenter`;
the de Longchamps point is `(2 : ℝ) • (O -ᵥ H) +ᵥ H`; the anticomplementary triangle is any
triangle whose vertices are the images of `A, B, C` under `AffineMap.homothety G (-2)`.
Each is proved from the corresponding library theorem. The `l14w_*` theorems are explicit
witnesses in `EuclideanSpace ℝ (Fin 2)` (non-vacuity); the `l14b_*` lemmas are helpers.
-/

open Affine EuclideanGeometry AffineMap
open scoped RealInnerProductSpace

namespace NagelLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ### Restatements -/

/-- A1: the three Gergonne cevians pass through the explicit Gergonne point. -/
theorem l14_gergonne (t : Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a := dist B C; let b := dist C A; let c := dist A B; let s := (a + b + c) / 2
    let Ge := Finset.univ.affineCombination ℝ t.points
      fun i => (s - ![a, b, c] i)⁻¹ / ∑ j, (s - ![a, b, c] j)⁻¹
    (∀ i, Ge ∈ line[ℝ, t.points i, t.touchpoint ∅ i]) ∧
      ∃ X : P, ∀ i, X ∈ line[ℝ, t.points i, t.touchpoint ∅ i] :=
  ⟨gergonnePoint_mem_cevian t, gergonne_cevians_concurrent t⟩

/-- A2: the three Nagel cevians pass through the explicit Nagel point. -/
theorem l14_nagel (t : Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a := dist B C; let b := dist C A; let c := dist A B; let s := (a + b + c) / 2
    let N := Finset.univ.affineCombination ℝ t.points fun i => (s - ![a, b, c] i) / s
    (∀ i, N ∈ line[ℝ, t.points i, t.touchpoint {i} i]) ∧
      ∃ X : P, ∀ i, X ∈ line[ℝ, t.points i, t.touchpoint {i} i] :=
  ⟨nagelPoint_mem_cevian t, nagel_cevians_concurrent t⟩

/-- A3: the Nagel line, `N - G = 2 (G - I)` and `I, G, N` collinear. -/
theorem l14_nagelLine (t : Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a := dist B C; let b := dist C A; let c := dist A B; let s := (a + b + c) / 2
    let N := Finset.univ.affineCombination ℝ t.points fun i => (s - ![a, b, c] i) / s
    let G := Finset.univ.centroid ℝ t.points
    N -ᵥ G = (2 : ℝ) • (G -ᵥ t.incenter) ∧ Collinear ℝ {t.incenter, G, N} :=
  ⟨nagelPoint_vsub_centroid t, collinear_incenter_centroid_nagelPoint t⟩

/-- A4: the Spieker centre (incentre of the medial triangle) is the midpoint of `I N`, hence on
the Nagel line. -/
theorem l14_spieker (t : Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a := dist B C; let b := dist C A; let c := dist A B; let s := (a + b + c) / 2
    let N := Finset.univ.affineCombination ℝ t.points fun i => (s - ![a, b, c] i) / s
    t.medial.incenter = midpoint ℝ t.incenter N ∧ Collinear ℝ {t.medial.incenter, t.incenter, N} :=
  ⟨medial_incenter_eq_midpoint t, collinear_spiekerCenter_incenter_nagelPoint t⟩

/-- C1: the de Longchamps point `L = 2 O - H`: `O` is the midpoint of `H L`, `L` lies on the Euler
line, and `L` is the orthocentre of the anticomplementary triangle. -/
theorem l14_deLongchamps (t : Triangle ℝ P) :
    let O := t.circumcenter; let H := t.orthocenter; let G := Finset.univ.centroid ℝ t.points
    let L := (2 : ℝ) • (O -ᵥ H) +ᵥ H
    midpoint ℝ H L = O ∧ Collinear ℝ {L, O, H} ∧ Collinear ℝ {G, O, L} ∧
      ∀ T : Triangle ℝ P, (∀ i, T.points i = homothety G (-2 : ℝ) (t.points i)) →
        T.orthocenter = L := by
  refine ⟨midpoint_orthocenter_deLongchampsPoint t,
    collinear_deLongchampsPoint_circumcenter_orthocenter t,
    collinear_centroid_circumcenter_deLongchampsPoint t, fun T hT => ?_⟩
  have e : T = t.anticomplementary := Simplex.ext fun i => by
    rw [hT]; simp [Triangle.anticomplementary]
  rw [e]; exact anticomplementary_orthocenter t

/-- C2: the Nagel point of the medial triangle is the incentre. -/
theorem l14_medial_nagel (t : Triangle ℝ P) :
    let M := t.medial
    let a := dist (M.points 1) (M.points 2); let b := dist (M.points 2) (M.points 0)
    let c := dist (M.points 0) (M.points 1); let s := (a + b + c) / 2
    Finset.univ.affineCombination ℝ M.points (fun i => (s - ![a, b, c] i) / s) = t.incenter :=
  medial_nagelPoint t

/-- C2: the incircle and excircle contact points on each side are symmetric about its midpoint
(isotomic). -/
theorem l14_isotomic (t : Triangle ℝ P) :
    midpoint ℝ (t.touchpoint ∅ 0) (t.touchpoint {0} 0) = midpoint ℝ (t.points 1) (t.points 2) ∧
    midpoint ℝ (t.touchpoint ∅ 1) (t.touchpoint {1} 1) = midpoint ℝ (t.points 2) (t.points 0) ∧
    midpoint ℝ (t.touchpoint ∅ 2) (t.touchpoint {2} 2) = midpoint ℝ (t.points 0) (t.points 1) :=
  ⟨midpoint_touchpoint_zero t, midpoint_touchpoint_one t, midpoint_touchpoint_two t⟩

/-- C3: the Nagel point is the incentre of the anticomplementary triangle. -/
theorem l14_nagel_anticomplementary (t : Triangle ℝ P) :
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a := dist B C; let b := dist C A; let c := dist A B; let s := (a + b + c) / 2
    let N := Finset.univ.affineCombination ℝ t.points fun i => (s - ![a, b, c] i) / s
    let G := Finset.univ.centroid ℝ t.points
    ∀ T : Triangle ℝ P, (∀ i, T.points i = homothety G (-2 : ℝ) (t.points i)) →
      T.incenter = N := by
  intro A B C a b c s N G T hT
  have e : T = t.anticomplementary := Simplex.ext fun i => by
    rw [hT]; simp [G, Triangle.anticomplementary]
  rw [e]; exact (nagelPoint_eq_anticomplementary_incenter t).symm

/-- C4: the Spieker centre has equal power with respect to the three excircles. -/
theorem l14_spieker_radical (t : Triangle ℝ P) (i j : Fin 3) :
    dist t.medial.incenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 =
      dist t.medial.incenter (t.exsphere {j}).center ^ 2 - t.exradius {j} ^ 2 :=
  spiekerCenter_power_exsphere t i j

/-! ### Witnesses -/


theorem l14b_dist_sq (x y : EuclideanSpace ℝ (Fin 2)) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

theorem l14b_not_collinear (X Y Z : EuclideanSpace ℝ (Fin 2))
    (h : (Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0) ≠ 0) :
    ¬ Collinear ℝ ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) := by
  intro hc
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at hc
  obtain ⟨v, hv⟩ := hc
  obtain ⟨r, hr⟩ := hv Y (by simp)
  obtain ⟨s, hs⟩ := hv Z (by simp)
  apply h
  have h0 := congrArg (· 0) hr; have h1 := congrArg (· 1) hr
  have h2 := congrArg (· 0) hs; have h3 := congrArg (· 1) hs
  simp only [vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1 h2 h3
  rw [h0, h1, h2, h3]; ring

theorem l14b_ne (X Y : EuclideanSpace ℝ (Fin 2)) (h : X 0 ≠ Y 0 ∨ X 1 ≠ Y 1) : X ≠ Y := by
  rintro rfl; tauto

theorem l14b_eq (X : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) (h0 : X 0 = a) (h1 : X 1 = b) : X = !₂[a, b] := by
  ext i; fin_cases i <;> simp [h0, h1]

theorem l14b_ac (t : Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (w : Fin 3 → ℝ) (hw : w 0 + w 1 + w 2 = 1) :
    Finset.univ.affineCombination ℝ t.points w =
      !₂[w 0 * t.points 0 0 + w 1 * t.points 1 0 + w 2 * t.points 2 0,
        w 0 * t.points 0 1 + w 1 * t.points 1 1 + w 2 * t.points 2 1] := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa [Fin.sum_univ_three] using hw)]
  ext i; fin_cases i <;> simp [Fin.sum_univ_three]

theorem l14b_lineMap (X Y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    AffineMap.lineMap X Y r = !₂[X 0 + r * (Y 0 - X 0), X 1 + r * (Y 1 - X 1)] := by
  rw [AffineMap.lineMap_apply_module']
  ext i; fin_cases i <;> simp <;> ring

theorem l14b_ne' (X Y : EuclideanSpace ℝ (Fin 2)) (h : X 0 ≠ Y 0 ∨ X 1 ≠ Y 1) : X ≠ Y := by
  rintro rfl; tauto

theorem l14b_dist (x y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 ≤ r)
    (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = r ^ 2) : dist x y = r := by
  rw [← sq_eq_sq₀ dist_nonneg hr, l14b_dist_sq, h]

theorem l14b_tri345 : ¬ Collinear ℝ ({!₂[0, 0], !₂[4, 0], !₂[0, 3]} : Set (EuclideanSpace ℝ (Fin 2))) :=
  l14b_not_collinear _ _ _ (by simp)

/-- The 3-4-5 witness triangle `A = (0,0)`, `B = (4,0)`, `C = (0,3)`. -/
noncomputable def l14T : Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![!₂[0, 0], !₂[4, 0], !₂[0, 3]], affineIndependent_iff_not_collinear_set.2 l14b_tri345⟩

theorem l14T_a : sideA l14T = 5 := l14b_dist _ _ _ (by norm_num) (by simp [l14T]; norm_num)
theorem l14T_b : sideB l14T = 3 := l14b_dist _ _ _ (by norm_num) (by simp [l14T])
theorem l14T_c : sideC l14T = 4 := l14b_dist _ _ _ (by norm_num) (by simp [l14T])
theorem l14T_s : semiperimeter l14T = 6 := by
  rw [semiperimeter, l14T_a, l14T_b, l14T_c]; norm_num

theorem l14T_I : l14T.incenter = !₂[1, 1] := by
  rw [incenter_eq_affineCombination]
  simp only [side, l14T_s, l14T_a, l14T_b, l14T_c]
  rw [l14b_ac _ _ (by simp; norm_num)]
  simp [l14T]; norm_num

theorem l14T_N : Finset.univ.affineCombination ℝ l14T.points
    (fun i => ((dist (l14T.points 1) (l14T.points 2) + dist (l14T.points 2) (l14T.points 0) +
      dist (l14T.points 0) (l14T.points 1)) / 2 - ![dist (l14T.points 1) (l14T.points 2),
      dist (l14T.points 2) (l14T.points 0), dist (l14T.points 0) (l14T.points 1)] i) /
      ((dist (l14T.points 1) (l14T.points 2) + dist (l14T.points 2) (l14T.points 0) +
      dist (l14T.points 0) (l14T.points 1)) / 2)) = !₂[2, 1] := by
  have ha : dist (l14T.points 1) (l14T.points 2) = 5 := l14T_a
  have hb : dist (l14T.points 2) (l14T.points 0) = 3 := l14T_b
  have hc : dist (l14T.points 0) (l14T.points 1) = 4 := l14T_c
  rw [ha, hb, hc, l14b_ac _ _ (by simp; norm_num)]
  simp [l14T]; norm_num

theorem l14T_Ge : Finset.univ.affineCombination ℝ l14T.points
    (fun i => (((dist (l14T.points 1) (l14T.points 2) + dist (l14T.points 2) (l14T.points 0) +
      dist (l14T.points 0) (l14T.points 1)) / 2 - ![dist (l14T.points 1) (l14T.points 2),
      dist (l14T.points 2) (l14T.points 0), dist (l14T.points 0) (l14T.points 1)] i)⁻¹ /
      ∑ j, ((dist (l14T.points 1) (l14T.points 2) + dist (l14T.points 2) (l14T.points 0) +
      dist (l14T.points 0) (l14T.points 1)) / 2 - ![dist (l14T.points 1) (l14T.points 2),
      dist (l14T.points 2) (l14T.points 0), dist (l14T.points 0) (l14T.points 1)] j)⁻¹)) =
    !₂[8/11, 9/11] := by
  have ha : dist (l14T.points 1) (l14T.points 2) = 5 := l14T_a
  have hb : dist (l14T.points 2) (l14T.points 0) = 3 := l14T_b
  have hc : dist (l14T.points 0) (l14T.points 1) = 4 := l14T_c
  rw [ha, hb, hc, l14b_ac _ _ (by simp [Fin.sum_univ_three]; norm_num)]
  simp [l14T, Fin.sum_univ_three]; norm_num

theorem l14T_G : Finset.univ.centroid ℝ l14T.points = !₂[4/3, 1] := by
  rw [Finset.centroid, l14b_ac _ _ (by simp; norm_num)]
  simp [l14T]; norm_num

theorem l14T_touch :
    l14T.touchpoint ∅ 0 = !₂[8/5, 9/5] ∧ l14T.touchpoint ∅ 1 = !₂[0, 1] ∧
    l14T.touchpoint ∅ 2 = !₂[1, 0] ∧ l14T.touchpoint {0} 0 = !₂[12/5, 6/5] ∧
    l14T.touchpoint {1} 1 = !₂[0, 2] ∧ l14T.touchpoint {2} 2 = !₂[3, 0] := by
  rw [touchpoint_empty_zero, touchpoint_empty_one, touchpoint_empty_two,
    touchpoint_singleton_zero, touchpoint_singleton_one, touchpoint_singleton_two]
  simp only [l14T_s, l14T_a, l14T_b, l14T_c, l14b_lineMap]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (ext i; fin_cases i <;> simp [l14T] <;> norm_num)


/-- Witness (A1–A4, C2): for the 3-4-5 triangle `A = (0,0)`, `B = (4,0)`, `C = (0,3)`
(`a = 5`, `b = 3`, `c = 4`, `s = 6`): the Gergonne point is `(8/11, 9/11)`, the Nagel point
`(2, 1)`, the incentre `(1, 1)`, the centroid `(4/3, 1)`, the Spieker centre `(3/2, 1)`; the
contact points are as listed; each pair of Gergonne (resp. Nagel) cevians is a pair of distinct
lines (vertex `j` is not on cevian `i`); `I ≠ G ≠ N ≠ I` (the Nagel line is a genuine line); and the
incircle and excircle contact points on each side are distinct. -/
theorem l14w_nagel :
    ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] →
    let A := t.points 0; let B := t.points 1; let C := t.points 2
    let a := dist B C; let b := dist C A; let c := dist A B; let s := (a + b + c) / 2
    let Ge := Finset.univ.affineCombination ℝ t.points
      fun i => (s - ![a, b, c] i)⁻¹ / ∑ j, (s - ![a, b, c] j)⁻¹
    let N := Finset.univ.affineCombination ℝ t.points fun i => (s - ![a, b, c] i) / s
    let G := Finset.univ.centroid ℝ t.points
    a = 5 ∧ b = 3 ∧ c = 4 ∧
    Ge = !₂[8/11, 9/11] ∧ N = !₂[2, 1] ∧ t.incenter = !₂[1, 1] ∧ G = !₂[4/3, 1] ∧
    t.medial.incenter = !₂[3/2, 1] ∧
    t.touchpoint ∅ 0 = !₂[8/5, 9/5] ∧ t.touchpoint ∅ 1 = !₂[0, 1] ∧
    t.touchpoint ∅ 2 = !₂[1, 0] ∧ t.touchpoint {0} 0 = !₂[12/5, 6/5] ∧
    t.touchpoint {1} 1 = !₂[0, 2] ∧ t.touchpoint {2} 2 = !₂[3, 0] ∧
    (∀ i j, i ≠ j → ¬ Collinear ℝ {t.points i, t.touchpoint ∅ i, t.points j}) ∧
    (∀ i j, i ≠ j → ¬ Collinear ℝ {t.points i, t.touchpoint {i} i, t.points j}) ∧
    t.incenter ≠ G ∧ G ≠ N ∧ N ≠ t.incenter ∧ Ge ≠ N ∧
    (∀ i, t.touchpoint ∅ i ≠ t.touchpoint {i} i) := by
  intro t ht
  obtain rfl : t = l14T := Simplex.ext fun i => by rw [ht]; rfl
  intro A B C a b c s Ge N G
  have hG : G = !₂[4/3, 1] := l14T_G
  have hN : N = !₂[2, 1] := l14T_N
  have hGe : Ge = !₂[8/11, 9/11] := l14T_Ge
  obtain ⟨d0, d1, d2, e0, e1, e2⟩ := l14T_touch
  have hS : l14T.medial.incenter = !₂[3/2, 1] := by
    rw [(l14_spieker l14T).1, l14T_I, l14T_N, midpoint_eq_smul_add]
    ext i; fin_cases i <;> simp <;> norm_num
  refine ⟨l14T_a, l14T_b, l14T_c, l14T_Ge, l14T_N, l14T_I, l14T_G, hS, d0, d1, d2, e0, e1, e2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have key : ∀ i, l14T.touchpoint ∅ i = ![!₂[8/5, 9/5], !₂[0, 1], !₂[1, 0]] i := by
      intro i; fin_cases i
      exacts [d0, d1, d2]
    intro i j hij
    rw [key]
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (apply l14b_not_collinear; simp [l14T]; try norm_num)
  · have key : ∀ i, l14T.touchpoint {i} i = ![!₂[12/5, 6/5], !₂[0, 2], !₂[3, 0]] i := by
      intro i; fin_cases i
      exacts [e0, e1, e2]
    intro i j hij
    rw [key]
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | (apply l14b_not_collinear; simp [l14T]; try norm_num)
  · rw [l14T_I, hG]; apply l14b_ne; simp; norm_num
  · rw [hG, hN]; apply l14b_ne; simp; norm_num
  · rw [l14T_I, hN]; apply l14b_ne; simp
  · rw [hGe, hN]; apply l14b_ne; simp; norm_num
  · intro i; fin_cases i
    · show l14T.touchpoint ∅ 0 ≠ l14T.touchpoint {0} 0
      rw [d0, e0]; apply l14b_ne; simp
    · show l14T.touchpoint ∅ 1 ≠ l14T.touchpoint {1} 1
      rw [d1, e1]; apply l14b_ne; simp
    · show l14T.touchpoint ∅ 2 ≠ l14T.touchpoint {2} 2
      rw [d2, e2]; apply l14b_ne; simp

/-- Witness (C2): for the 3-4-5 triangle the Nagel point of the medial triangle is `(1, 1)` (the
incentre), which differs from the incentre `(3/2, 1)` of the medial triangle (the Spieker centre). -/
theorem l14w_medial_nagel :
    ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] →
    let M := t.medial
    let a := dist (M.points 1) (M.points 2); let b := dist (M.points 2) (M.points 0)
    let c := dist (M.points 0) (M.points 1); let s := (a + b + c) / 2
    Finset.univ.affineCombination ℝ M.points (fun i => (s - ![a, b, c] i) / s) = !₂[1, 1] ∧
      M.incenter = !₂[3/2, 1] ∧ !₂[1, 1] ≠ (!₂[3/2, 1] : EuclideanSpace ℝ (Fin 2)) := by
  intro t ht
  obtain rfl : t = l14T := Simplex.ext fun i => by rw [ht]; rfl
  obtain ⟨-, -, -, -, -, -, -, hS, -⟩ := l14w_nagel l14T rfl
  refine ⟨(l14_medial_nagel l14T).trans l14T_I, hS, ?_⟩
  apply l14b_ne; simp; norm_num

theorem l14b_tri_anti : ¬ Collinear ℝ ({!₂[4, 3], !₂[-4, 3], !₂[4, -3]} : Set (EuclideanSpace ℝ (Fin 2))) :=
  l14b_not_collinear _ _ _ (by simp; norm_num)

/-- Witness (C3): for the 3-4-5 triangle the anticomplementary triangle (vertices `(4, 3)`,
`(-4, 3)`, `(4, -3)`, the images of `A, B, C` under the homothety `G, -2`) exists, and its
incentre is the Nagel point `(2, 1)`, which is not the incentre `(1, 1)` of `t`. -/
theorem l14w_nagel_anticomplementary :
    ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] →
    let G := Finset.univ.centroid ℝ t.points
    ∃ T : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), T.points = ![!₂[4, 3], !₂[-4, 3], !₂[4, -3]] ∧
      (∀ i, T.points i = homothety G (-2 : ℝ) (t.points i)) ∧
      T.incenter = !₂[2, 1] ∧ T.incenter ≠ t.incenter := by
  intro t ht
  obtain rfl : t = l14T := Simplex.ext fun i => by rw [ht]; rfl
  intro G
  let T : Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ⟨![!₂[4, 3], !₂[-4, 3], !₂[4, -3]], affineIndependent_iff_not_collinear_set.2 l14b_tri_anti⟩
  have hT : ∀ i, T.points i = homothety G (-2 : ℝ) (l14T.points i) := by
    have hG : G = !₂[4/3, 1] := l14T_G
    intro i; rw [hG, homothety_apply]
    fin_cases i <;> (ext j; fin_cases j <;> simp [T, l14T] <;> norm_num)
  have hI : T.incenter = !₂[2, 1] := (l14_nagel_anticomplementary l14T T hT).trans l14T_N
  refine ⟨T, rfl, hT, hI, ?_⟩
  rw [hI, l14T_I]; apply l14b_ne; simp

/-- Witness (C4): for the 3-4-5 triangle the three excircles have centres `(6, 6)`, `(-2, 2)`,
`(3, -3)` and radii `6`, `2`, `3` (three distinct circles), and the Spieker centre `(3/2, 1)` has
power `37/4` with respect to each. -/
theorem l14w_spieker_radical :
    ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[0, 3]] →
    t.medial.incenter = !₂[3/2, 1] ∧
    (t.exsphere {0}).center = !₂[6, 6] ∧ (t.exsphere {1}).center = !₂[-2, 2] ∧
    (t.exsphere {2}).center = !₂[3, -3] ∧
    t.exradius {0} = 6 ∧ t.exradius {1} = 2 ∧ t.exradius {2} = 3 ∧
    ∀ i, dist t.medial.incenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 = 37 / 4 := by
  intro t ht
  obtain rfl : t = l14T := Simplex.ext fun i => by rw [ht]; rfl
  obtain ⟨-, -, -, -, -, -, -, hS, -⟩ := l14w_nagel l14T rfl
  have hc : ∀ i, (l14T.exsphere {i}).center = ![!₂[6, 6], !₂[-2, 2], !₂[3, -3]] i := by
    intro i
    rw [Simplex.exsphere_center, excenter_singleton_eq_affineCombination]
    fin_cases i <;>
    · simp only [side, l14T_s, l14T_a, l14T_b, l14T_c]
      rw [l14b_ac _ _ (by simp; norm_num)]
      ext j; fin_cases j <;> simp [l14T] <;> norm_num
  have hr : ∀ i, l14T.exradius {i} = ![6, 2, 3] i := by
    intro i
    have h := exradius_singleton_sq l14T i
    rw [l14T_s, l14T_a, l14T_b, l14T_c] at h
    fin_cases i <;>
    · simp only [side, l14T_a, l14T_b, l14T_c] at h ⊢
      norm_num at h ⊢
      refine (sq_eq_sq₀ (l14T.exradius_nonneg _) (by norm_num)).1 ?_
      rw [h]; norm_num
  refine ⟨hS, hc 0, hc 1, hc 2, hr 0, hr 1, hr 2, fun i => ?_⟩
  have h := spiekerCenter_power_exsphere_eq l14T i
  rw [l14T_s, l14T_a, l14T_b, l14T_c] at h
  simp only [Triangle.spiekerCenter] at h
  rw [h]; norm_num


theorem l14b_tri2 : ¬ Collinear ℝ ({!₂[0, 0], !₂[4, 0], !₂[1, 3]} : Set (EuclideanSpace ℝ (Fin 2))) :=
  l14b_not_collinear _ _ _ (by simp)

theorem l14b_tri2_anti : ¬ Collinear ℝ ({!₂[5, 3], !₂[-3, 3], !₂[3, -3]} : Set (EuclideanSpace ℝ (Fin 2))) :=
  l14b_not_collinear _ _ _ (by simp; norm_num)

/-- Witness (C1): for the scalene triangle `A = (0,0)`, `B = (4,0)`, `C = (1,3)`: `O = (2, 1)`,
`H = (1, 1)` (so `O ≠ H`), the de Longchamps point is `L = (3, 1)`, distinct from `O`, `H` and `G`;
the anticomplementary triangle `(5, 3)`, `(-3, 3)`, `(3, -3)` exists and has orthocentre `L`. -/
theorem l14w_deLongchamps :
    ∀ t : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), t.points = ![!₂[0, 0], !₂[4, 0], !₂[1, 3]] →
    let O := t.circumcenter; let H := t.orthocenter; let G := Finset.univ.centroid ℝ t.points
    let L := (2 : ℝ) • (O -ᵥ H) +ᵥ H
    O = !₂[2, 1] ∧ H = !₂[1, 1] ∧ G = !₂[5/3, 1] ∧ L = !₂[3, 1] ∧
    L ≠ O ∧ L ≠ H ∧ O ≠ H ∧ L ≠ G ∧
    ∃ T : Triangle ℝ (EuclideanSpace ℝ (Fin 2)), T.points = ![!₂[5, 3], !₂[-3, 3], !₂[3, -3]] ∧
      (∀ i, T.points i = homothety G (-2 : ℝ) (t.points i)) ∧ T.orthocenter = L := by
  intro t ht O H G L
  have hO : O = !₂[2, 1] := by
    refine (t.eq_circumcenter_of_dist_eq (r := √5) ?_ ?_).symm
    · rw [t.span_eq_top (by simp)]; exact AffineSubspace.mem_top _ _ _
    · intro i
      rw [← sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num), l14b_dist_sq,
        ht]
      fin_cases i <;> simp <;> norm_num
  have hG : G = !₂[5/3, 1] := by
    show Finset.univ.centroid ℝ t.points = _
    rw [Finset.centroid, l14b_ac _ _ (by simp; norm_num), ht]
    simp; norm_num
  have hH : H = !₂[1, 1] := by
    show t.orthocenter = _
    rw [Triangle.orthocenter_eq_smul_vsub_vadd_circumcenter]
    change (3 : ℝ) • (G -ᵥ O) +ᵥ O = _
    rw [hG, hO]; ext i; fin_cases i <;> simp <;> norm_num
  have hL : L = !₂[3, 1] := by
    show (2 : ℝ) • (O -ᵥ H) +ᵥ H = _
    rw [hO, hH]; ext i; fin_cases i <;> simp <;> norm_num
  let T : Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ⟨![!₂[5, 3], !₂[-3, 3], !₂[3, -3]], affineIndependent_iff_not_collinear_set.2 l14b_tri2_anti⟩
  have hT : ∀ i, T.points i = homothety G (-2 : ℝ) (t.points i) := by
    intro i; rw [hG, homothety_apply, ht]
    fin_cases i <;> (ext j; fin_cases j <;> simp [T] <;> norm_num)
  refine ⟨hO, hH, hG, hL, ?_, ?_, ?_, ?_, T, rfl, hT, ((l14_deLongchamps t).2.2.2 T hT)⟩
  · rw [hL, hO]; apply l14b_ne; simp
  · rw [hL, hH]; apply l14b_ne; simp
  · rw [hO, hH]; apply l14b_ne; simp
  · rw [hL, hG]; apply l14b_ne; simp; norm_num

end NagelLine
