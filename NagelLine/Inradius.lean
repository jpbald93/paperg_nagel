import NagelLine.Extensions

/-!
# Inradius form of the Spieker radical-centre value

The squared inradius is `r² = (s - a)(s - b)(s - c) / s`, so the common power of the Spieker
centre with respect to the three excircles is `(s² + r²) / 4`.
-/

open Affine EuclideanGeometry AffineMap
open scoped RealInnerProductSpace

namespace NagelLine

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- The squared inradius is `(s - a)(s - b)(s - c) / s`. -/
theorem inradius_sq (t : Triangle ℝ P) :
    t.inradius ^ 2 = (semiperimeter t - sideA t) * (semiperimeter t - sideB t) *
      (semiperimeter t - sideC t) / semiperimeter t := by
  have hK := (dblArea_pos t).ne'
  have hs := (semiperimeter_pos t).ne'
  have hK2 : dblArea t ^ 2 = 4 * semiperimeter t * (semiperimeter t - sideA t) *
      (semiperimeter t - sideB t) * (semiperimeter t - sideC t) := by
    rw [dblArea, height0_sq, heron_factor]
  have hsum : ∑ i, t.excenterWeightsUnnorm ∅ i = 2 * semiperimeter t / dblArea t := by
    simp only [Affine.Simplex.excenterWeightsUnnorm_empty_apply, height_eq, inv_div]
    rw [Fin.sum_univ_three]
    simp only [side, semiperimeter]
    simp
    field_simp
  rw [Affine.Simplex.inradius, Affine.Simplex.exsphere_radius,
    Affine.Simplex.exradius_eq_abs_inv_sum, sq_abs, hsum, inv_div, div_pow, hK2]
  field_simp
  ring

/-- The power of the Spieker centre with respect to each excircle is `(s² + r²) / 4`, with `r`
the inradius. -/
theorem spiekerCenter_power_exsphere_eq_inradius (t : Triangle ℝ P) (i : Fin 3) :
    dist t.spiekerCenter (t.exsphere {i}).center ^ 2 - t.exradius {i} ^ 2 =
      (semiperimeter t ^ 2 + t.inradius ^ 2) / 4 := by
  rw [spiekerCenter_power_exsphere_eq, inradius_sq]

end NagelLine
