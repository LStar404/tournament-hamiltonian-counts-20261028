module

public import TournamentHamiltonian.RootObservable.Fubini

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootObservable
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral ForestQuartic PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

/-- Genuine full-to-grounded observable transport, before normalization.
The only hypotheses are ordinary measurability and integrability of the actual weights. -/
theorem observable_integral (F : EdgeSet (n+1)) (f : (Fin n → ℝ) → ℝ)
    (hfm : Measurable f)
    (hr : Integrable (fun x => realKernel (rootMatrix F) 0 x * f x))
    (hf : Integrable (fun y => kernelDensity F y * f (rootCoordinates y))) :
    (∫ y, kernelDensity F y * f (rootCoordinates y)) =
      jacobianFactor n * ∫ x, realKernel (rootMatrix F) 0 x * f x := by
  rw [integral_split_root _ hf]
  have hs (t : ℝ) := tail_substitution (fun y => kernelDensity F y * f (rootCoordinates y)) t
  simp only [kernel_reconstruct, rootCoordinates_reconstruct] at hs
  simp_rw [hs]
  rw [integral_const_mul]
  simp_rw [mul_assoc]
  rw [shifted_product_integral _ hr (by unfold realKernel Matrix.mulVec dotProduct; fun_prop)
    _ (by fun_prop)]
  unfold jacobianFactor
  ring

theorem jacobianFactor_pos (n : ℕ) : 0 < jacobianFactor n := by
  unfold jacobianFactor modeMass
  positivity

theorem normalization_transport (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) :
    normalization (K F) = jacobianFactor n * normalization (rootMatrix F) := by
  have h := observable_integral F (fun _ => 1) measurable_const
    (by simpa using realKernel_integrable (rootMatrix_posDef F hm) (0 : Fin n → ℝ))
    (by simpa [kernelDensity] using realKernel_integrable (K_posDef F hm) (0 : Fin (n+1) → ℝ))
  simpa only [mul_one, kernelDensity, zero_integral (K_posDef F hm),
    zero_integral (rootMatrix_posDef F hm)] using h

/-- The exact normalized expectation identity; determinant equality alone is not used as transport. -/
theorem observable_integral_ratio (F : EdgeSet (n+1)) (hm : 8 ≤ n+1)
    (f : (Fin n → ℝ) → ℝ) (hfm : Measurable f)
    (hr : Integrable (fun x => realKernel (rootMatrix F) 0 x * f x))
    (hf : Integrable (fun y => kernelDensity F y * f (rootCoordinates y))) :
    (∫ y, kernelDensity F y * f (rootCoordinates y)) / normalization (K F) =
      (∫ x, realKernel (rootMatrix F) 0 x * f x) / normalization (rootMatrix F) := by
  rw [observable_integral F f hfm hr hf, normalization_transport F hm]
  exact mul_div_mul_left _ _ (jacobianFactor_pos n).ne'

theorem kernel_mul_bounded_integrable {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (f : (ι → ℝ) → ℝ) (hfm : Measurable f)
    (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable (fun x => realKernel A 0 x * f x) := by
  apply ((realKernel_integrable hA 0).mul_const C).mono' (by unfold realKernel Matrix.mulVec dotProduct; fun_prop)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  change |Real.exp _| * |f x| ≤ Real.exp _ * C
  rw [abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb x) (Real.exp_nonneg _)

/-- A directly usable observable class: bounded measurable functions, with no integral premises. -/
theorem bounded_observable_integral_ratio (F : EdgeSet (n+1)) (hm : 8 ≤ n+1)
    (f : (Fin n → ℝ) → ℝ) (hfm : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    (∫ y, kernelDensity F y * f (rootCoordinates y)) / normalization (K F) =
      (∫ x, realKernel (rootMatrix F) 0 x * f x) / normalization (rootMatrix F) := by
  apply observable_integral_ratio F hm f hfm
  · exact kernel_mul_bounded_integrable (rootMatrix_posDef F hm) f hfm C hb
  · exact kernel_mul_bounded_integrable (K_posDef F hm) (fun y => f (rootCoordinates y))
      (hfm.comp (by unfold rootCoordinates; fun_prop)) C (fun y => hb _)

end RootObservable
