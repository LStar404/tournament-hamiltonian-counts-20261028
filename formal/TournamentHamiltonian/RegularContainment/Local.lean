module

public import TournamentHamiltonian.RegularContainment.Bridge

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularContainment
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral PDGaussian RootGaussianTail RootObservable Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

lemma local_difference_bound (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    ‖torusIntegrand F x - (quarticConstant:ℂ)*phaseKernel (rootMatrix F) (rootImbalance F) x‖ ≤
      LocalLogCos.phaseError F x + realKernel (rootMatrix F) 0 x*rootExpDeviation F x := by
  let P := phaseKernel (rootMatrix F) (rootImbalance F) x
  let q : ℂ := Real.exp (-rootQuartic F x)
  have he : torusIntegrand F x-(quarticConstant:ℂ)*P =
      (torusIntegrand F x-P*q)+P*(q-(quarticConstant:ℂ)) := by ring
  rw [he]
  apply (norm_add_le _ _).trans_eq
  rw [norm_mul, phase_norm]
  congr 1
  · rw [torusIntegrand_phasedProduct]; rfl
  · simp only [q, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simp only [rootExpDeviation, quarticConstant, neg_div]

/-- Actual local signed integral, with the quartic correction replaced in L1. -/
theorem local_integral_bound (F : EdgeSet (n+1)) (hm : 16 ≤ n+1)
    (r : ℝ) (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8) :
    ‖(∫ x in rootCube n r, torusIntegrand F x) -
      (quarticConstant:ℂ)*(∫ x in rootCube n r, phaseKernel (rootMatrix F) (rootImbalance F) x)‖ ≤
      (LocalLogCos.errorBudget (n+1) r + ForestQuartic.errorRate (n+1))*normalization (rootMatrix F) := by
  have hm8 : 8 ≤ n+1 := by omega
  have hsub : rootCube n r ⊆ rootCube n (Real.pi/2) := rootCube_mono (by linarith [Real.pi_pos])
  have hi := (torusIntegrand_integrableOn F).mono_set hsub
  have hp := (forest_integrable F hm8).integrableOn (s := rootCube n r)
  have hd := root_expDeviation_integrable F hm8
  have he := LocalLogCos.phaseError_integrableOn F hm8 hr hrp
  change IntegrableOn (LocalLogCos.phaseError F) (rootCube n r) at he
  rw [← integral_const_mul, ← integral_sub hi (hp.const_mul (quarticConstant:ℂ))]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hc := integral_mono (hi.sub (hp.const_mul (quarticConstant:ℂ))).norm
    (he.add hd.integrableOn) (local_difference_bound F)
  simp only [Pi.add_apply, Pi.sub_apply] at hc
  rw [integral_add he hd.integrableOn] at hc
  have hfull : (∫ x in rootCube n r, realKernel (rootMatrix F) 0 x*rootExpDeviation F x) ≤
      ∫ x, realKernel (rootMatrix F) 0 x*rootExpDeviation F x := by
    exact integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (fun x => mul_nonneg (realKernel_nonneg F x) (rootExpDeviation_nonneg F x))) hd
  have hq := root_expDeviation_bound_unnormalized F hm
  have ht := LocalLogCos.phaseError_integral_bound F hm8 hr hrp
  change (∫ x in rootCube n r, LocalLogCos.phaseError F x) ≤ _ at ht
  nlinarith

/-- The global Gaussian characteristic integral can be recovered from its local box. -/
theorem phase_tail_bound (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) (r : ℝ) (hr : 0 ≤ r) :
    ‖(∫ x in rootCube n r, phaseKernel (rootMatrix F) (rootImbalance F) x) -
      (∫ x, phaseKernel (rootMatrix F) (rootImbalance F) x)‖ ≤
        gaussianTailBudget (n+1) r*Z (n+1) 1 := by
  have hs := integral_add_compl (rootCube_measurable n r) (forest_integrable F hm)
  have he : (∫ x in rootCube n r, phaseKernel (rootMatrix F) (rootImbalance F) x) -
      (∫ x, phaseKernel (rootMatrix F) (rootImbalance F) x) =
      -(∫ x in (rootCube n r)ᶜ, phaseKernel (rootMatrix F) (rootImbalance F) x) := by rw [← hs]; ring
  rw [he, norm_neg]
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (rootCube n r)ᶜ)
    (phaseKernel (rootMatrix F) (rootImbalance F))
  simp only [phase_norm] at hn
  exact hn.trans (gaussian_tail_bound F hm r hr)

/-- Actual torus tail has exactly D's absolute kernel as its controlling integral. -/
theorem torus_tail_bound (F : EdgeSet (n+1)) (r : ℝ) (hrp : r ≤ Real.pi/2) :
    ‖torusIntegral F - ∫ x in rootCube n r, torusIntegrand F x‖ ≤
      UniformTorusTail.tailIntegral (graph F) r := by
  have hs := integral_inter_add_sdiff (rootCube_measurable n r) (torusIntegrand_integrableOn F)
  rw [inter_eq_right.mpr (rootCube_mono hrp)] at hs
  rw [torusIntegral_eq, ← hs, add_sub_cancel_left]
  rw [tailIntegral_eq]
  exact norm_integral_le_integral_norm _

end RegularContainment
