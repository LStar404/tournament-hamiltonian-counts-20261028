module

public import TournamentHamiltonian.ForestQuartic.Law

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ForestQuartic
open MeasureTheory ProbabilityTheory Matrix GaussianQuartic ForestGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem empty_weight (m : ℕ) (z : Fin m → ℝ) : weight (emptyEdgeSet m) z = 1 := by
  simp [weight, exponent, emptyEdgeSet_laplacian]

theorem empty_tilted_measure (m : ℕ) : tiltedMeasure (emptyEdgeSet m) = gaussian (Fin m) := by
  unfold tiltedMeasure
  have he : exponent (emptyEdgeSet m) = 0 := by
    funext z
    simp [exponent, emptyEdgeSet_laplacian]
  rw [he, tilted_zero]

theorem empty_removed (m : ℕ) (z : Fin m → ℝ) : removedQuartic (emptyEdgeSet m) z = 0 := by
  simp [removedQuartic, emptyEdgeSet]

theorem empty_forestQuartic (m : ℕ) (z : Fin m → ℝ) : forestQuartic (emptyEdgeSet m) z = quartic m z := by
  have h := forest_add_removed (emptyEdgeSet m) z
  simpa only [empty_removed, add_zero] using h

/-- Exact second moment includes variance plus the nonzero finite-size bias squared. -/
theorem complete_deviation_second_exact (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, (quartic m z-1/2)^2 ∂gaussian (Fin m)) =
      (26*(m : ℝ)^2-11*m-12)/(12*(m : ℝ)^3) := quartic_deviation_second m hm

theorem complete_deviation_order_one :
    (∫ z, (quartic 1 z-1/2)^2 ∂gaussian (Fin 1)) = 1/4 := by
  rw [complete_deviation_second_exact 1 (by norm_num)]
  norm_num

theorem complete_deviation_order_two :
    (∫ z, (quartic 2 z-1/2)^2 ∂gaussian (Fin 2)) = 35/48 := by
  rw [complete_deviation_second_exact 2 (by norm_num)]
  norm_num

theorem complete_deviation_order_sixteen :
    (∫ z, (quartic 16 z-1/2)^2 ∂gaussian (Fin 16)) = 539/4096 := by
  rw [complete_deviation_second_exact 16 (by norm_num)]
  norm_num

theorem empty_deviation_order_two :
    (∫ z, (forestQuartic (emptyEdgeSet 2) z-1/2)^2 ∂tiltedMeasure (emptyEdgeSet 2)) = 35/48 := by
  simp_rw [empty_tilted_measure, empty_forestQuartic]
  exact complete_deviation_order_two

theorem tilted_characteristic_at_zero {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) :
    (∫ z, Complex.exp (Complex.I*((0 : Fin m → ℝ) ⬝ᵥ z : ℝ)) ∂tiltedMeasure F) = 1 := by
  rw [tilted_characteristic F hm]
  simp

theorem tilted_MGF_at_zero {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) :
    (∫ z, Real.exp ((0 : Fin m → ℝ) ⬝ᵥ z) ∂tiltedMeasure F) = 1 := by
  rw [tilted_MGF F hm]
  simp

theorem cutoff_sixteen_bound (F : EdgeSet 16) :
    (∫ z, expDeviation F z ∂tiltedMeasure F) ≤
      Real.exp 4*(Real.sqrt (3/16) + Real.sqrt 1680/192) := by
  have h := expDeviation_bound F (by norm_num)
  simpa only [errorRate, Nat.cast_ofNat, show (12 : ℝ)*16=192 by norm_num] using h
end ForestQuartic
