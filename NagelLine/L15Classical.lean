import NagelLine.Basic
import NagelLine.Main
import NagelLine.Extensions
import NagelLine.L14

/-!
# Layer 15: classical statements (Paper G, Group N) and new uniqueness proofs

Source: the classical file `PaperGClassical.lean`, sha256 2bb545d76d505fe0…
Its basic definitions are copied verbatim into the namespace `NagelLine.Classical`. The only
textual change: the classical file's local abbreviation `Pt` is written out in full as
`EuclideanSpace ℝ (Fin 2)`, because the library sources may not extend the parser. The terms are the same.
Each `cov_*` theorem has the classical statement verbatim and is proved from library theorems
(`NagelLine.*`), plus bridge lemmas and new proofs given here. New proofs: `cevian_unique`,
`nagel_unique` (uniqueness of the Nagel point as the common point of the cevians), `medial_indep`
and `anti_indep` (the classical extra non-degeneracy hypotheses are redundant).
Ported from the scratch file `l15_nagel/scratch/L15_compare.lean`.
-/

open EuclideanGeometry

noncomputable section

namespace NagelLine.Classical

/-! ## Basic definitions -/

/-- The triangle `ABC` as a Mathlib `Affine.Triangle`. -/
def ClassicalTri (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨![A, B, C], h⟩

/-- The point with (unnormalised) barycentric coordinates `wA : wB : wC` with respect to
`A, B, C` (meaningful when `wA + wB + wC ≠ 0`). -/
def ClassicalBary (A B C : (EuclideanSpace ℝ (Fin 2))) (wA wB wC : ℝ) : (EuclideanSpace ℝ (Fin 2)) :=
  Finset.univ.affineCombination ℝ ![A, B, C] (fun i => ![wA, wB, wC] i / (wA + wB + wC))

/-- Semiperimeter. -/
def ClassicalSemiperimeter (A B C : (EuclideanSpace ℝ (Fin 2))) : ℝ := (dist B C + dist C A + dist A B) / 2

/-- Area `Δ = ½·AB·AC·sin A`. -/
def ClassicalArea (A B C : (EuclideanSpace ℝ (Fin 2))) : ℝ := (1 / 2) * dist A B * dist A C * Real.sin (∠ B A C)

/-- Centroid `G`. (Stated for any three points; also used for pedal triangles.) -/
def ClassicalCentroid (A B C : (EuclideanSpace ℝ (Fin 2))) : (EuclideanSpace ℝ (Fin 2)) := Finset.univ.centroid ℝ ![A, B, C]

/-- Excentre opposite `A`: barycentrics `-a : b : c` (textbook formula). -/
def ClassicalExcenterA (A B C : (EuclideanSpace ℝ (Fin 2))) : (EuclideanSpace ℝ (Fin 2)) :=
  ClassicalBary A B C (-dist B C) (dist C A) (dist A B)

/-- Point of contact of the excircle opposite `A` with line `BC`: the foot of the
perpendicular from the excentre to `BC`. -/
def ClassicalExContactA (A B C : (EuclideanSpace ℝ (Fin 2))) : (EuclideanSpace ℝ (Fin 2)) :=
  (orthogonalProjection line[ℝ, B, C] (ClassicalExcenterA A B C) : (EuclideanSpace ℝ (Fin 2)))

/-- Exradius `r_a`: distance from the excentre opposite `A` to line `BC`. -/
def ClassicalExradiusA (A B C : (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  dist (ClassicalExcenterA A B C) (ClassicalExContactA A B C)

/-- Point of contact of the incircle with line `BC`: foot of the perpendicular from the
(Mathlib) incentre to `BC`. -/
def ClassicalInContactA (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) : (EuclideanSpace ℝ (Fin 2)) :=
  (orthogonalProjection line[ℝ, B, C] (ClassicalTri A B C h).incenter : (EuclideanSpace ℝ (Fin 2)))

/-- Incircle contact points on `CA` and `AB` (feet of perpendiculars from the same incentre). -/
def ClassicalInContactB (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) : (EuclideanSpace ℝ (Fin 2)) :=
  (orthogonalProjection line[ℝ, C, A] (ClassicalTri A B C h).incenter : (EuclideanSpace ℝ (Fin 2)))

def ClassicalInContactC (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) : (EuclideanSpace ℝ (Fin 2)) :=
  (orthogonalProjection line[ℝ, A, B] (ClassicalTri A B C h).incenter : (EuclideanSpace ℝ (Fin 2)))

/-- A point (other than `A`, in a non-degenerate triangle) on the internal bisector of angle
`BAC`: `A + AB/|AB| + AC/|AC|`. -/
def ClassicalBisectorPoint (A B C : (EuclideanSpace ℝ (Fin 2))) : (EuclideanSpace ℝ (Fin 2)) :=
  ((dist A B)⁻¹ • (B -ᵥ A) + (dist A C)⁻¹ • (C -ᵥ A)) +ᵥ A

/-- Reflection of the line `AP` in the internal bisector at `A`
(the isogonal line of `AP` at vertex `A`). -/
def ClassicalIsogonalLine (A B C P : (EuclideanSpace ℝ (Fin 2))) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  line[ℝ, A, reflection line[ℝ, A, ClassicalBisectorPoint A B C] P]

/-- Symmedian through `A`: reflection of the median `A M_a` in the internal bisector at `A`. -/
def ClassicalSymmedian (A B C : (EuclideanSpace ℝ (Fin 2))) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ClassicalIsogonalLine A B C (midpoint ℝ B C)

/-- `P` and `Q` are isogonal conjugates: for each vertex, the reflection of the line
vertex–`P` in the bisector at that vertex passes through `Q`. -/
def ClassicalIsogonalConj (A B C P Q : (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Q ∈ ClassicalIsogonalLine A B C P ∧ Q ∈ ClassicalIsogonalLine B C A P ∧
    Q ∈ ClassicalIsogonalLine C A B P

/-- Pedal triangle vertex on line `BC` of a point `P`. -/
def ClassicalFoot (B C P : (EuclideanSpace ℝ (Fin 2))) : (EuclideanSpace ℝ (Fin 2)) := (orthogonalProjection line[ℝ, B, C] P : (EuclideanSpace ℝ (Fin 2)))

/-- Centroid of the pedal triangle of `P`. -/
def ClassicalPedalCentroid (A B C P : (EuclideanSpace ℝ (Fin 2))) : (EuclideanSpace ℝ (Fin 2)) :=
  ClassicalCentroid (ClassicalFoot B C P) (ClassicalFoot C A P) (ClassicalFoot A B P)

/-- Anticomplementary-triangle vertex opposite `A`: reflection of `A` in the midpoint of `BC`
(i.e. `B + C - A`); the triangle of these has `ABC` as medial triangle. -/
def ClassicalAnticompl (A B C : (EuclideanSpace ℝ (Fin 2))) : (EuclideanSpace ℝ (Fin 2)) := AffineEquiv.pointReflection ℝ (midpoint ℝ B C) A

/-! ## Bridge lemmas (new, scratch only) -/

open Affine AffineMap NagelLine

section Bridges

variable {A B C : (EuclideanSpace ℝ (Fin 2))} (h : AffineIndependent ℝ ![A, B, C])

lemma proj_congr {S T : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))} [Nonempty S] [Nonempty T]
    [S.direction.HasOrthogonalProjection] [T.direction.HasOrthogonalProjection]
    (hST : S = T) (p : (EuclideanSpace ℝ (Fin 2))) :
    (orthogonalProjection S p : (EuclideanSpace ℝ (Fin 2))) = orthogonalProjection T p := by
  subst hST; rfl

lemma bary_lin (A B C : (EuclideanSpace ℝ (Fin 2))) (w : Fin 3 → ℝ) (hw : w 0 + w 1 + w 2 = 1) :
    Finset.univ.affineCombination ℝ ![A, B, C] w = w 0 • A + w 1 • B + w 2 • C := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _
    (by simpa [Fin.sum_univ_three] using hw)]
  simp [Fin.sum_univ_three]

lemma sA : sideA (ClassicalTri A B C h) = dist B C := rfl
lemma sB : sideB (ClassicalTri A B C h) = dist C A := rfl
lemma sC : sideC (ClassicalTri A B C h) = dist A B := rfl

lemma inA_eq : ClassicalInContactA A B C h = (ClassicalTri A B C h).touchpoint ∅ 0 := by
  unfold ClassicalInContactA Simplex.touchpoint Simplex.orthogonalProjectionSpan
  exact proj_congr (by rw [range_face0]; rfl) _

lemma inB_eq : ClassicalInContactB A B C h = (ClassicalTri A B C h).touchpoint ∅ 1 := by
  unfold ClassicalInContactB Simplex.touchpoint Simplex.orthogonalProjectionSpan
  exact proj_congr (by rw [range_face1]; rfl) _

lemma inC_eq : ClassicalInContactC A B C h = (ClassicalTri A B C h).touchpoint ∅ 2 := by
  unfold ClassicalInContactC Simplex.touchpoint Simplex.orthogonalProjectionSpan
  exact proj_congr (by rw [range_face2]; rfl) _

include h in
lemma tri_pos : 0 < dist C A + dist A B - dist B C ∧ 0 < dist B C + dist A B - dist C A ∧
    0 < dist B C + dist C A - dist A B := by
  have ha := s_sub_a_pos (ClassicalTri A B C h)
  have hb := s_sub_b_pos (ClassicalTri A B C h)
  have hc := s_sub_c_pos (ClassicalTri A B C h)
  rw [semiperimeter, sA, sB, sC] at ha hb hc
  refine ⟨by linarith, by linarith, by linarith⟩

lemma inv_helper {D : ℝ} (hD : D ≠ 0) : D * D⁻¹ = 1 := mul_inv_cancel₀ hD

lemma exA0 : ClassicalExcenterA A B C = (ClassicalTri A B C h).excenter {0} := by
  obtain ⟨ha, hb, hc⟩ := tri_pos h
  rw [excenter_singleton_eq_affineCombination]
  unfold ClassicalExcenterA ClassicalBary
  change Finset.univ.affineCombination ℝ ![A, B, C] _ = Finset.univ.affineCombination ℝ ![A, B, C] _
  
  congr 1; funext i
  generalize hx : dist B C = x at *
  generalize hy : dist C A = y at *
  generalize hz : dist A B = z at *
  fin_cases i <;> simp [side, semiperimeter, sA, sB, sC, hx, hy, hz] <;>
    field_simp <;> ring

lemma exA1 : ClassicalExcenterA B C A = (ClassicalTri A B C h).excenter {1} := by
  obtain ⟨ha, hb, hc⟩ := tri_pos h
  rw [excenter_singleton_eq_affineCombination]
  unfold ClassicalExcenterA ClassicalBary
  change Finset.univ.affineCombination ℝ ![B, C, A] _ = Finset.univ.affineCombination ℝ ![A, B, C] _
  simp only [side, semiperimeter, sA, sB, sC]
  generalize hx : dist B C = x at *
  generalize hy : dist C A = y at *
  generalize hz : dist A B = z at *
  have n1 : -y + z + x ≠ 0 := by linarith
  have n2 : x - y + z ≠ 0 := by linarith
  have n3 : -z + x + y ≠ 0 := by linarith
  have n4 : x + y - z ≠ 0 := by linarith
  have n5 : (x + y + z) / 2 - y ≠ 0 := by linarith
  have n6 : (x + y + z) / 2 - z ≠ 0 := by linarith
  have : -x + y + z ≠ 0 := by linarith
  have : -x + z + y ≠ 0 := by linarith
  have : y - x + z ≠ 0 := by linarith
  have : y + z - x ≠ 0 := by linarith
  have : z - x + y ≠ 0 := by linarith
  have : z + y - x ≠ 0 := by linarith
  have : x - y + z ≠ 0 := by linarith
  have : x + z - y ≠ 0 := by linarith
  have : -y + x + z ≠ 0 := by linarith
  have : -y + z + x ≠ 0 := by linarith
  have : z + x - y ≠ 0 := by linarith
  have : z - y + x ≠ 0 := by linarith
  have : x + y - z ≠ 0 := by linarith
  have : x - z + y ≠ 0 := by linarith
  have : y + x - z ≠ 0 := by linarith
  have : y - z + x ≠ 0 := by linarith
  have : -z + x + y ≠ 0 := by linarith
  have : -z + y + x ≠ 0 := by linarith
  have d0 : x - y + z ≠ 0 := by linarith
  have d1 : -y + z + x ≠ 0 := by linarith
  have d2 : z - y + x ≠ 0 := by linarith
  have d3 : x + y - z ≠ 0 := by linarith
  have d4 : -z + x + y ≠ 0 := by linarith
  have d5 : x - z + y ≠ 0 := by linarith
  have d6 : y - z + x ≠ 0 := by linarith
  rw [bary_lin _ _ _ _ (by simp; field_simp; try ring),
    bary_lin _ _ _ _ (by simp; field_simp; try first
      | (linear_combination inv_helper d0)
      | (linear_combination x * inv_helper d0)
      | (linear_combination (-x) * inv_helper d0)
      | (linear_combination y * inv_helper d0)
      | (linear_combination (-y) * inv_helper d0)
      | (linear_combination z * inv_helper d0)
      | (linear_combination (-z) * inv_helper d0)
      | (linear_combination inv_helper d1)
      | (linear_combination x * inv_helper d1)
      | (linear_combination (-x) * inv_helper d1)
      | (linear_combination y * inv_helper d1)
      | (linear_combination (-y) * inv_helper d1)
      | (linear_combination z * inv_helper d1)
      | (linear_combination (-z) * inv_helper d1)
      | (linear_combination inv_helper d2)
      | (linear_combination x * inv_helper d2)
      | (linear_combination (-x) * inv_helper d2)
      | (linear_combination y * inv_helper d2)
      | (linear_combination (-y) * inv_helper d2)
      | (linear_combination z * inv_helper d2)
      | (linear_combination (-z) * inv_helper d2)
      | (linear_combination inv_helper d3)
      | (linear_combination x * inv_helper d3)
      | (linear_combination (-x) * inv_helper d3)
      | (linear_combination y * inv_helper d3)
      | (linear_combination (-y) * inv_helper d3)
      | (linear_combination z * inv_helper d3)
      | (linear_combination (-z) * inv_helper d3)
      | (linear_combination inv_helper d4)
      | (linear_combination x * inv_helper d4)
      | (linear_combination (-x) * inv_helper d4)
      | (linear_combination y * inv_helper d4)
      | (linear_combination (-y) * inv_helper d4)
      | (linear_combination z * inv_helper d4)
      | (linear_combination (-z) * inv_helper d4)
      | (linear_combination inv_helper d5)
      | (linear_combination x * inv_helper d5)
      | (linear_combination (-x) * inv_helper d5)
      | (linear_combination y * inv_helper d5)
      | (linear_combination (-y) * inv_helper d5)
      | (linear_combination z * inv_helper d5)
      | (linear_combination (-z) * inv_helper d5)
      | (linear_combination inv_helper d6)
      | (linear_combination x * inv_helper d6)
      | (linear_combination (-x) * inv_helper d6)
      | (linear_combination y * inv_helper d6)
      | (linear_combination (-y) * inv_helper d6)
      | (linear_combination z * inv_helper d6)
      | (linear_combination (-z) * inv_helper d6))]
  simp
  match_scalars <;> field_simp <;> first
    | (linear_combination inv_helper d0)
    | (linear_combination x * inv_helper d0)
    | (linear_combination (-x) * inv_helper d0)
    | (linear_combination y * inv_helper d0)
    | (linear_combination (-y) * inv_helper d0)
    | (linear_combination z * inv_helper d0)
    | (linear_combination (-z) * inv_helper d0)
    | (linear_combination inv_helper d1)
    | (linear_combination x * inv_helper d1)
    | (linear_combination (-x) * inv_helper d1)
    | (linear_combination y * inv_helper d1)
    | (linear_combination (-y) * inv_helper d1)
    | (linear_combination z * inv_helper d1)
    | (linear_combination (-z) * inv_helper d1)
    | (linear_combination inv_helper d2)
    | (linear_combination x * inv_helper d2)
    | (linear_combination (-x) * inv_helper d2)
    | (linear_combination y * inv_helper d2)
    | (linear_combination (-y) * inv_helper d2)
    | (linear_combination z * inv_helper d2)
    | (linear_combination (-z) * inv_helper d2)
    | (linear_combination inv_helper d3)
    | (linear_combination x * inv_helper d3)
    | (linear_combination (-x) * inv_helper d3)
    | (linear_combination y * inv_helper d3)
    | (linear_combination (-y) * inv_helper d3)
    | (linear_combination z * inv_helper d3)
    | (linear_combination (-z) * inv_helper d3)
    | (linear_combination inv_helper d4)
    | (linear_combination x * inv_helper d4)
    | (linear_combination (-x) * inv_helper d4)
    | (linear_combination y * inv_helper d4)
    | (linear_combination (-y) * inv_helper d4)
    | (linear_combination z * inv_helper d4)
    | (linear_combination (-z) * inv_helper d4)
    | (linear_combination inv_helper d5)
    | (linear_combination x * inv_helper d5)
    | (linear_combination (-x) * inv_helper d5)
    | (linear_combination y * inv_helper d5)
    | (linear_combination (-y) * inv_helper d5)
    | (linear_combination z * inv_helper d5)
    | (linear_combination (-z) * inv_helper d5)
    | (linear_combination inv_helper d6)
    | (linear_combination x * inv_helper d6)
    | (linear_combination (-x) * inv_helper d6)
    | (linear_combination y * inv_helper d6)
    | (linear_combination (-y) * inv_helper d6)
    | (linear_combination z * inv_helper d6)
    | (linear_combination (-z) * inv_helper d6)

lemma exA2 : ClassicalExcenterA C A B = (ClassicalTri A B C h).excenter {2} := by
  obtain ⟨ha, hb, hc⟩ := tri_pos h
  rw [excenter_singleton_eq_affineCombination]
  unfold ClassicalExcenterA ClassicalBary
  change Finset.univ.affineCombination ℝ ![C, A, B] _ = Finset.univ.affineCombination ℝ ![A, B, C] _
  simp only [side, semiperimeter, sA, sB, sC]
  generalize hx : dist B C = x at *
  generalize hy : dist C A = y at *
  generalize hz : dist A B = z at *
  have n1 : -y + z + x ≠ 0 := by linarith
  have n2 : x - y + z ≠ 0 := by linarith
  have n3 : -z + x + y ≠ 0 := by linarith
  have n4 : x + y - z ≠ 0 := by linarith
  have n5 : (x + y + z) / 2 - y ≠ 0 := by linarith
  have n6 : (x + y + z) / 2 - z ≠ 0 := by linarith
  have : -x + y + z ≠ 0 := by linarith
  have : -x + z + y ≠ 0 := by linarith
  have : y - x + z ≠ 0 := by linarith
  have : y + z - x ≠ 0 := by linarith
  have : z - x + y ≠ 0 := by linarith
  have : z + y - x ≠ 0 := by linarith
  have : x - y + z ≠ 0 := by linarith
  have : x + z - y ≠ 0 := by linarith
  have : -y + x + z ≠ 0 := by linarith
  have : -y + z + x ≠ 0 := by linarith
  have : z + x - y ≠ 0 := by linarith
  have : z - y + x ≠ 0 := by linarith
  have : x + y - z ≠ 0 := by linarith
  have : x - z + y ≠ 0 := by linarith
  have : y + x - z ≠ 0 := by linarith
  have : y - z + x ≠ 0 := by linarith
  have : -z + x + y ≠ 0 := by linarith
  have : -z + y + x ≠ 0 := by linarith
  have d0 : x - y + z ≠ 0 := by linarith
  have d1 : -y + z + x ≠ 0 := by linarith
  have d2 : z - y + x ≠ 0 := by linarith
  have d3 : x + y - z ≠ 0 := by linarith
  have d4 : -z + x + y ≠ 0 := by linarith
  have d5 : x - z + y ≠ 0 := by linarith
  have d6 : y - z + x ≠ 0 := by linarith
  rw [bary_lin _ _ _ _ (by simp; field_simp; try ring),
    bary_lin _ _ _ _ (by simp; field_simp; try first
      | (linear_combination inv_helper d0)
      | (linear_combination x * inv_helper d0)
      | (linear_combination (-x) * inv_helper d0)
      | (linear_combination y * inv_helper d0)
      | (linear_combination (-y) * inv_helper d0)
      | (linear_combination z * inv_helper d0)
      | (linear_combination (-z) * inv_helper d0)
      | (linear_combination inv_helper d1)
      | (linear_combination x * inv_helper d1)
      | (linear_combination (-x) * inv_helper d1)
      | (linear_combination y * inv_helper d1)
      | (linear_combination (-y) * inv_helper d1)
      | (linear_combination z * inv_helper d1)
      | (linear_combination (-z) * inv_helper d1)
      | (linear_combination inv_helper d2)
      | (linear_combination x * inv_helper d2)
      | (linear_combination (-x) * inv_helper d2)
      | (linear_combination y * inv_helper d2)
      | (linear_combination (-y) * inv_helper d2)
      | (linear_combination z * inv_helper d2)
      | (linear_combination (-z) * inv_helper d2)
      | (linear_combination inv_helper d3)
      | (linear_combination x * inv_helper d3)
      | (linear_combination (-x) * inv_helper d3)
      | (linear_combination y * inv_helper d3)
      | (linear_combination (-y) * inv_helper d3)
      | (linear_combination z * inv_helper d3)
      | (linear_combination (-z) * inv_helper d3)
      | (linear_combination inv_helper d4)
      | (linear_combination x * inv_helper d4)
      | (linear_combination (-x) * inv_helper d4)
      | (linear_combination y * inv_helper d4)
      | (linear_combination (-y) * inv_helper d4)
      | (linear_combination z * inv_helper d4)
      | (linear_combination (-z) * inv_helper d4)
      | (linear_combination inv_helper d5)
      | (linear_combination x * inv_helper d5)
      | (linear_combination (-x) * inv_helper d5)
      | (linear_combination y * inv_helper d5)
      | (linear_combination (-y) * inv_helper d5)
      | (linear_combination z * inv_helper d5)
      | (linear_combination (-z) * inv_helper d5)
      | (linear_combination inv_helper d6)
      | (linear_combination x * inv_helper d6)
      | (linear_combination (-x) * inv_helper d6)
      | (linear_combination y * inv_helper d6)
      | (linear_combination (-y) * inv_helper d6)
      | (linear_combination z * inv_helper d6)
      | (linear_combination (-z) * inv_helper d6))]
  simp
  match_scalars <;> field_simp <;> first
    | (linear_combination inv_helper d0)
    | (linear_combination x * inv_helper d0)
    | (linear_combination (-x) * inv_helper d0)
    | (linear_combination y * inv_helper d0)
    | (linear_combination (-y) * inv_helper d0)
    | (linear_combination z * inv_helper d0)
    | (linear_combination (-z) * inv_helper d0)
    | (linear_combination inv_helper d1)
    | (linear_combination x * inv_helper d1)
    | (linear_combination (-x) * inv_helper d1)
    | (linear_combination y * inv_helper d1)
    | (linear_combination (-y) * inv_helper d1)
    | (linear_combination z * inv_helper d1)
    | (linear_combination (-z) * inv_helper d1)
    | (linear_combination inv_helper d2)
    | (linear_combination x * inv_helper d2)
    | (linear_combination (-x) * inv_helper d2)
    | (linear_combination y * inv_helper d2)
    | (linear_combination (-y) * inv_helper d2)
    | (linear_combination z * inv_helper d2)
    | (linear_combination (-z) * inv_helper d2)
    | (linear_combination inv_helper d3)
    | (linear_combination x * inv_helper d3)
    | (linear_combination (-x) * inv_helper d3)
    | (linear_combination y * inv_helper d3)
    | (linear_combination (-y) * inv_helper d3)
    | (linear_combination z * inv_helper d3)
    | (linear_combination (-z) * inv_helper d3)
    | (linear_combination inv_helper d4)
    | (linear_combination x * inv_helper d4)
    | (linear_combination (-x) * inv_helper d4)
    | (linear_combination y * inv_helper d4)
    | (linear_combination (-y) * inv_helper d4)
    | (linear_combination z * inv_helper d4)
    | (linear_combination (-z) * inv_helper d4)
    | (linear_combination inv_helper d5)
    | (linear_combination x * inv_helper d5)
    | (linear_combination (-x) * inv_helper d5)
    | (linear_combination y * inv_helper d5)
    | (linear_combination (-y) * inv_helper d5)
    | (linear_combination z * inv_helper d5)
    | (linear_combination (-z) * inv_helper d5)
    | (linear_combination inv_helper d6)
    | (linear_combination x * inv_helper d6)
    | (linear_combination (-x) * inv_helper d6)
    | (linear_combination y * inv_helper d6)
    | (linear_combination (-y) * inv_helper d6)
    | (linear_combination z * inv_helper d6)
    | (linear_combination (-z) * inv_helper d6)

lemma exC0 : ClassicalExContactA A B C = (ClassicalTri A B C h).touchpoint {0} 0 := by
  unfold ClassicalExContactA
  rw [exA0 h]
  unfold Simplex.touchpoint Simplex.orthogonalProjectionSpan
  exact proj_congr (by rw [range_face0]; rfl) _

lemma exC1 : ClassicalExContactA B C A = (ClassicalTri A B C h).touchpoint {1} 1 := by
  unfold ClassicalExContactA
  rw [exA1 h]
  unfold Simplex.touchpoint Simplex.orthogonalProjectionSpan
  exact proj_congr (by rw [range_face1]; rfl) _

lemma exC2 : ClassicalExContactA C A B = (ClassicalTri A B C h).touchpoint {2} 2 := by
  unfold ClassicalExContactA
  rw [exA2 h]
  unfold Simplex.touchpoint Simplex.orthogonalProjectionSpan
  exact proj_congr (by rw [range_face2]; rfl) _

/-- NEW PROOF: two cevians from distinct vertices `A`, `B` (the first meeting line `BC` at a
point `D ≠ B`) meet in at most one point. -/
lemma cevian_unique {A B C D E X Y : (EuclideanSpace ℝ (Fin 2))} (hABC : ¬ Collinear ℝ {A, B, C})
    (hD : D ∈ line[ℝ, B, C]) (hBD : B ≠ D)
    (hXA : X ∈ line[ℝ, A, D]) (hYA : Y ∈ line[ℝ, A, D])
    (hXB : X ∈ line[ℝ, B, E]) (hYB : Y ∈ line[ℝ, B, E]) : X = Y := by
  by_contra hXY
  have c1 : Collinear ℝ {X, Y, A, D} := collinear_insert_insert_of_mem_affineSpan_pair hXA hYA
  have c2 : Collinear ℝ {X, Y, B, E} := collinear_insert_insert_of_mem_affineSpan_pair hXB hYB
  have hA : A ∈ line[ℝ, X, Y] := c1.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hXY
  have hD' : D ∈ line[ℝ, X, Y] :=
    c1.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hXY
  have hB : B ∈ line[ℝ, X, Y] := c2.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hXY
  have c3 : Collinear ℝ {D, B, C} := collinear_insert_of_mem_affineSpan_pair hD
  have hCBD : C ∈ line[ℝ, B, D] := c3.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBD
  have hC : C ∈ line[ℝ, X, Y] := (affineSpan_pair_le_of_mem_of_mem hB hD') hCBD
  exact hABC (collinear_triple_of_mem_affineSpan_pair hA hB hC)

/-- NEW PROOF: any common point of the first two classical Nagel cevians is the repository's
`nagelPoint`. -/
lemma nagel_unique {X : (EuclideanSpace ℝ (Fin 2))} (hX0 : X ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hX1 : X ∈ line[ℝ, B, ClassicalExContactA B C A]) :
    X = (ClassicalTri A B C h).nagelPoint := by
  set t := ClassicalTri A B C h
  rw [exC0 h] at hX0
  rw [exC1 h] at hX1
  have n0 : t.nagelPoint ∈ line[ℝ, A, t.touchpoint {0} 0] := nagelPoint_mem_cevian t 0
  have n1 : t.nagelPoint ∈ line[ℝ, B, t.touchpoint {1} 1] := nagelPoint_mem_cevian t 1
  have hs : Sbtw ℝ B (t.touchpoint {0} 0) C := sbtw_touchpoint_singleton_zero t
  exact cevian_unique (affineIndependent_iff_not_collinear_set.1 h) hs.wbtw.mem_affineSpan
    hs.left_ne hX0 n0 hX1 n1

lemma centroid_lin : Finset.univ.centroid ℝ ![A, B, C] =
    (3⁻¹ : ℝ) • A + (3⁻¹ : ℝ) • B + (3⁻¹ : ℝ) • C := by
  rw [Finset.centroid_def, bary_lin _ _ _ _ (by simp [Finset.centroidWeights_apply]; norm_num)]
  simp [Finset.centroidWeights_apply]

lemma medial_points_eq (i : Fin 3) : (ClassicalTri A B C h).medial.points i =
    ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B] i := by
  rw [Simplex.medial_points, Simplex.faceOppositeCentroid_eq_smul_vsub_vadd_point]
  change _ • (Finset.univ.centroid ℝ ![A, B, C] -ᵥ _) +ᵥ Finset.univ.centroid ℝ ![A, B, C] = _
  rw [centroid_lin]
  fin_cases i <;> simp [ClassicalTri, midpoint_eq_smul_add, vsub_eq_sub, vadd_eq_add] <;> module

include h in
/-- NEW PROOF (cheap): the medial triangle is non-degenerate (the classical extra hypothesis
`hM` is provable from `h`). -/
lemma medial_indep : AffineIndependent ℝ ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B] := by
  have e : ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B] = (ClassicalTri A B C h).medial.points :=
    funext fun i => (medial_points_eq h i).symm
  rw [e]; exact (ClassicalTri A B C h).medial.independent

lemma medial_eq (hM : AffineIndependent ℝ ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B]) :
    ClassicalTri _ _ _ hM = (ClassicalTri A B C h).medial :=
  Simplex.ext fun i => (medial_points_eq h i).symm

lemma anti_points_eq (i : Fin 3) : (ClassicalTri A B C h).anticomplementary.points i =
    ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B] i := by
  fin_cases i
  · show (ClassicalTri A B C h).anticomplementary.points 0 = ClassicalAnticompl A B C
    rw [anticomplementary_points_zero]
    simp [ClassicalTri, ClassicalAnticompl, Equiv.pointReflection_apply,
      midpoint_eq_smul_add, vsub_eq_sub, vadd_eq_add]; module
  · show (ClassicalTri A B C h).anticomplementary.points 1 = ClassicalAnticompl B C A
    rw [anticomplementary_points_one]
    simp [ClassicalTri, ClassicalAnticompl, Equiv.pointReflection_apply,
      midpoint_eq_smul_add, vsub_eq_sub, vadd_eq_add]; module
  · show (ClassicalTri A B C h).anticomplementary.points 2 = ClassicalAnticompl C A B
    rw [anticomplementary_points_two]
    simp [ClassicalTri, ClassicalAnticompl, Equiv.pointReflection_apply,
      midpoint_eq_smul_add, vsub_eq_sub, vadd_eq_add]; module

include h in
/-- NEW PROOF (cheap): the anticomplementary triangle is non-degenerate (`hT` provable). -/
lemma anti_indep : AffineIndependent ℝ
    ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B] := by
  have e : ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B] =
      (ClassicalTri A B C h).anticomplementary.points :=
    funext fun i => (anti_points_eq h i).symm
  rw [e]; exact (ClassicalTri A B C h).anticomplementary.independent

lemma anti_eq (hT : AffineIndependent ℝ
      ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B]) :
    ClassicalTri _ _ _ hT = (ClassicalTri A B C h).anticomplementary :=
  Simplex.ext fun i => (anti_points_eq h i).symm

lemma col_of_mem {p q x y : (EuclideanSpace ℝ (Fin 2))} (hx : x ∈ line[ℝ, p, q]) (hy : y ∈ line[ℝ, p, q])
    (s : Set (EuclideanSpace ℝ (Fin 2))) (hs : s ⊆ {x, y, p, q}) : Collinear ℝ s :=
  (collinear_insert_insert_of_mem_affineSpan_pair hx hy).subset hs

end Bridges

lemma centroid_eq_lineMap (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    Finset.univ.centroid ℝ t.points = lineMap t.incenter t.nagelPoint (1 / 3 : ℝ) := by
  rw [lineMap_apply, eq_comm, ← vsub_left_cancel_iff (p := t.incenter), vadd_vsub,
    ← vsub_add_vsub_cancel t.nagelPoint (Finset.univ.centroid ℝ t.points) t.incenter,
    nagelPoint_vsub_centroid]
  module

lemma O_H_lineMap (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    Finset.univ.centroid ℝ t.points = lineMap t.circumcenter t.orthocenter (1 / 3 : ℝ) ∧
      AffineEquiv.pointReflection ℝ t.circumcenter t.orthocenter =
        lineMap t.circumcenter t.orthocenter (-1 : ℝ) := by
  constructor
  · rw [lineMap_apply, orthocenter_vsub_circumcenter, smul_smul]; norm_num
  · rw [lineMap_apply, AffineEquiv.pointReflection_apply, ← neg_vsub_eq_vsub_rev, neg_one_smul]

lemma deLongchamps_eq (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    t.deLongchampsPoint = AffineEquiv.pointReflection ℝ t.circumcenter t.orthocenter := by
  rw [Triangle.deLongchampsPoint, AffineEquiv.pointReflection_apply,
    ← vsub_left_cancel_iff (p := t.orthocenter), vadd_vsub, vadd_vsub_assoc, two_smul]

/-! ## Group N: classical statements (verbatim) proved from repository theorems -/

/-- N1 (E). -/
theorem cov_N1 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ Ge : (EuclideanSpace ℝ (Fin 2)), Ge ∈ line[ℝ, A, ClassicalInContactA A B C h] ∧
      Ge ∈ line[ℝ, B, ClassicalInContactB A B C h] ∧
      Ge ∈ line[ℝ, C, ClassicalInContactC A B C h] := by
  obtain ⟨hGe, -⟩ := l14_gergonne (ClassicalTri A B C h)
  rw [inA_eq h, inB_eq h, inC_eq h]
  exact ⟨_, hGe 0, hGe 1, hGe 2⟩

/-- N2a (E). -/
theorem cov_N2a (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    ∃ Na : (EuclideanSpace ℝ (Fin 2)), Na ∈ line[ℝ, A, ClassicalExContactA A B C] ∧
      Na ∈ line[ℝ, B, ClassicalExContactA B C A] ∧
      Na ∈ line[ℝ, C, ClassicalExContactA C A B] := by
  obtain ⟨hN, -⟩ := l14_nagel (ClassicalTri A B C h)
  rw [exC0 h, exC1 h, exC2 h]
  exact ⟨_, hN 0, hN 1, hN 2⟩

/-- N2b (E, via the repository's explicit contact-point theorem `touchpoint_singleton_zero`). -/
theorem cov_N2b (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    dist B (ClassicalExContactA A B C) = ClassicalSemiperimeter A B C - dist A B ∧
      dist C (ClassicalExContactA A B C) = ClassicalSemiperimeter A B C - dist C A := by
  set t := ClassicalTri A B C h
  have ha : 0 < dist B C := sideA_pos t
  obtain ⟨-, hb, hc⟩ := tri_pos h
  rw [exC0 h, touchpoint_singleton_zero]
  change dist B (lineMap B C _) = _ ∧ dist C (lineMap B C _) = _
  rw [dist_comm B, dist_comm C, dist_lineMap_left, dist_lineMap_right]
  simp only [semiperimeter, ClassicalSemiperimeter, sA, sB, sC]
  have hBC : dist B C ≠ 0 := ha.ne'
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) ha.le),
    abs_of_nonneg (by rw [sub_nonneg, div_le_one ha]; linarith)]
  constructor <;> field_simp <;> ring

/-- N3 (E). Uses the NEW uniqueness lemma `nagel_unique` (classical `Na` = repository
`nagelPoint`), then the repository's `N - G = 2 (G - I)` and collinearity. -/
theorem cov_N3 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) (Na : (EuclideanSpace ℝ (Fin 2)))
    (hA : Na ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hB : Na ∈ line[ℝ, B, ClassicalExContactA B C A])
    (hC : Na ∈ line[ℝ, C, ClassicalExContactA C A B]) :
    Collinear ℝ {(ClassicalTri A B C h).incenter, ClassicalCentroid A B C, Na} ∧
      Wbtw ℝ (ClassicalTri A B C h).incenter (ClassicalCentroid A B C) Na ∧
      dist (ClassicalCentroid A B C) Na =
        2 * dist (ClassicalTri A B C h).incenter (ClassicalCentroid A B C) := by
  obtain rfl := nagel_unique h hA hB
  set t := ClassicalTri A B C h
  have hG : ClassicalCentroid A B C = Finset.univ.centroid ℝ t.points := rfl
  have hv := nagelPoint_vsub_centroid t
  rw [hG]
  refine ⟨collinear_incenter_centroid_nagelPoint t,
    ⟨1 / 3, ⟨by norm_num, by norm_num⟩, (centroid_eq_lineMap t).symm⟩, ?_⟩
  rw [dist_comm, dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2)), hv, norm_smul, dist_comm,
    dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2))]
  norm_num

/-- N4 (E). -/
theorem cov_N4 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C])
    (hM : AffineIndependent ℝ ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B]) (Na : (EuclideanSpace ℝ (Fin 2)))
    (hA : Na ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hB : Na ∈ line[ℝ, B, ClassicalExContactA B C A])
    (hC : Na ∈ line[ℝ, C, ClassicalExContactA C A B]) :
    (ClassicalTri _ _ _ hM).incenter = midpoint ℝ (ClassicalTri A B C h).incenter Na ∧
      Collinear ℝ {(ClassicalTri A B C h).incenter, ClassicalCentroid A B C, Na,
        (ClassicalTri _ _ _ hM).incenter} := by
  obtain rfl := nagel_unique h hA hB
  set t := ClassicalTri A B C h
  have hG : ClassicalCentroid A B C = Finset.univ.centroid ℝ t.points := rfl
  rw [medial_eq h hM, medial_incenter_eq_midpoint, hG, centroid_eq_lineMap]
  refine ⟨rfl, col_of_mem (p := t.incenter) (q := t.nagelPoint)
    (AffineMap.lineMap_mem_affineSpan_pair (1 / 3 : ℝ) _ _)
    (AffineMap.lineMap_mem_affineSpan_pair (⅟2 : ℝ) _ _) _ ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl <;> simp [midpoint, t]

/-- N5 (E), side `BC` as stated classically. -/
theorem cov_N5 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    midpoint ℝ (ClassicalInContactA A B C h) (ClassicalExContactA A B C) = midpoint ℝ B C := by
  rw [inA_eq h, exC0 h]
  exact midpoint_touchpoint_zero (ClassicalTri A B C h)

/-- N5 for all three sides (in the classical file's own notions; the classical file states
only `BC`). -/
theorem cov_N5_all (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) :
    midpoint ℝ (ClassicalInContactA A B C h) (ClassicalExContactA A B C) = midpoint ℝ B C ∧
    midpoint ℝ (ClassicalInContactB A B C h) (ClassicalExContactA B C A) = midpoint ℝ C A ∧
    midpoint ℝ (ClassicalInContactC A B C h) (ClassicalExContactA C A B) = midpoint ℝ A B := by
  rw [inA_eq h, exC0 h, inB_eq h, exC1 h, inC_eq h, exC2 h]
  exact (l14_isotomic (ClassicalTri A B C h))

/-- N6a (E). The NEW uniqueness lemma is applied to the medial triangle (whose
non-degeneracy `medial_indep` is also NEW). -/
theorem cov_N6a (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C]) (X : (EuclideanSpace ℝ (Fin 2)))
    (hA : X ∈ line[ℝ, midpoint ℝ B C,
      ClassicalExContactA (midpoint ℝ B C) (midpoint ℝ C A) (midpoint ℝ A B)])
    (hB : X ∈ line[ℝ, midpoint ℝ C A,
      ClassicalExContactA (midpoint ℝ C A) (midpoint ℝ A B) (midpoint ℝ B C)])
    (hC : X ∈ line[ℝ, midpoint ℝ A B,
      ClassicalExContactA (midpoint ℝ A B) (midpoint ℝ B C) (midpoint ℝ C A)]) :
    X = (ClassicalTri A B C h).incenter := by
  have hM := medial_indep h
  rw [nagel_unique hM hA hB, medial_eq h hM]
  exact medial_nagelPoint _

/-- N6b (E). -/
theorem cov_N6b (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C])
    (hT : AffineIndependent ℝ
      ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B])
    (Na : (EuclideanSpace ℝ (Fin 2)))
    (hA : Na ∈ line[ℝ, A, ClassicalExContactA A B C])
    (hB : Na ∈ line[ℝ, B, ClassicalExContactA B C A])
    (hC : Na ∈ line[ℝ, C, ClassicalExContactA C A B]) :
    Na = (ClassicalTri _ _ _ hT).incenter := by
  rw [nagel_unique h hA hB, anti_eq h hT]
  exact nagelPoint_eq_anticomplementary_incenter _

/-- N7 (E). `G = lineMap O H (1/3)` and `L = lineMap O H (-1)` (from the repository's
`orthocenter_vsub_circumcenter`), so all four points lie on `line[O, H]` with no case split
(when `O = H` the line degenerates to a point and the set is a singleton, still collinear). -/
theorem cov_N7 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C])
    (hT : AffineIndependent ℝ
      ![ClassicalAnticompl A B C, ClassicalAnticompl B C A, ClassicalAnticompl C A B]) :
    Collinear ℝ {(ClassicalTri A B C h).circumcenter, ClassicalCentroid A B C,
        (ClassicalTri A B C h).orthocenter,
        AffineEquiv.pointReflection ℝ (ClassicalTri A B C h).circumcenter
          (ClassicalTri A B C h).orthocenter} ∧
      AffineEquiv.pointReflection ℝ (ClassicalTri A B C h).circumcenter
          (ClassicalTri A B C h).orthocenter = (ClassicalTri _ _ _ hT).orthocenter := by
  set t := ClassicalTri A B C h
  have hG : ClassicalCentroid A B C = Finset.univ.centroid ℝ t.points := rfl
  obtain ⟨e1, e2⟩ := O_H_lineMap t
  refine ⟨?_, ?_⟩
  · rw [hG, e1, e2]
    refine col_of_mem (p := t.circumcenter) (q := t.orthocenter)
      (AffineMap.lineMap_mem_affineSpan_pair (1 / 3 : ℝ) _ _)
      (AffineMap.lineMap_mem_affineSpan_pair (-1 : ℝ) _ _) _ ?_
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
    tauto
  · rw [anti_eq h hT, anticomplementary_orthocenter, deLongchamps_eq]

/-- N8 (E). -/
theorem cov_N8 (A B C : (EuclideanSpace ℝ (Fin 2))) (h : AffineIndependent ℝ ![A, B, C])
    (hM : AffineIndependent ℝ ![midpoint ℝ B C, midpoint ℝ C A, midpoint ℝ A B]) :
    let Sp := (ClassicalTri _ _ _ hM).incenter
    dist Sp (ClassicalExcenterA A B C) ^ 2 - ClassicalExradiusA A B C ^ 2 =
        dist Sp (ClassicalExcenterA B C A) ^ 2 - ClassicalExradiusA B C A ^ 2 ∧
      dist Sp (ClassicalExcenterA B C A) ^ 2 - ClassicalExradiusA B C A ^ 2 =
        dist Sp (ClassicalExcenterA C A B) ^ 2 - ClassicalExradiusA C A B ^ 2 := by
  intro Sp
  set t := ClassicalTri A B C h
  have r0 : ClassicalExradiusA A B C = t.exradius {0} := by
    rw [ClassicalExradiusA, exA0 h, exC0 h]; exact (t.excenterExists_singleton 0).dist_excenter 0
  have r1 : ClassicalExradiusA B C A = t.exradius {1} := by
    rw [ClassicalExradiusA, exA1 h, exC1 h]; exact (t.excenterExists_singleton 1).dist_excenter 1
  have r2 : ClassicalExradiusA C A B = t.exradius {2} := by
    rw [ClassicalExradiusA, exA2 h, exC2 h]; exact (t.excenterExists_singleton 2).dist_excenter 2
  have hS : Sp = t.medial.incenter := by simp only [Sp]; rw [medial_eq h hM]
  rw [r0, r1, r2, exA0 h, exA1 h, exA2 h, hS]
  exact ⟨l14_spieker_radical t 0 1, l14_spieker_radical t 1 2⟩

end NagelLine.Classical
