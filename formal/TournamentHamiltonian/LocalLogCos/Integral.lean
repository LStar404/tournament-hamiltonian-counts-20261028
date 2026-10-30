module

public import TournamentHamiltonian.LocalLogCos.Scale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LocalLogCos
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral RootObservable PDGaussian Set
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

def rootBoxSet (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {x | rootBox r x}
def phaseError (F : EdgeSet (n+1)) (x : Fin n → ℝ) : ℝ :=
  ‖phasedProduct F x-phaseKernel (rootMatrix F) (rootImbalance F) x*(Real.exp (-rootQuartic F x) : ℂ)‖

theorem rootBoxSet_measurable (n : ℕ) (r : ℝ) : MeasurableSet (rootBoxSet n r) := by
  have he : rootBoxSet n r = ⋂ i : Fin n, {x | |x i|≤r} := by ext x; simp [rootBoxSet,rootBox]
  rw [he]
  exact MeasurableSet.iInter (fun i => (isClosed_le (continuous_apply i).abs continuous_const).measurableSet)

theorem phaseError_continuous (F : EdgeSet (n+1)) : Continuous (phaseError F) := by
  have hq := rootQuartic_continuous F
  unfold phaseError phasedProduct phaseKernel cosProduct rootLift Matrix.mulVec dotProduct
  fun_prop

theorem indicator_phaseError_le (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    (x : Fin n → ℝ) :
    (rootBoxSet n r).indicator (phaseError F) x ≤ errorBudget (n+1) r*realKernel (rootMatrix F) 0 x := by
  by_cases hx : x ∈ rootBoxSet n r
  · rw [indicator_of_mem hx]
    exact actual_phase_error F hr hrp hx
  · rw [indicator_of_notMem hx]
    unfold errorBudget realKernel
    positivity

/-- Actual ordinary-Lebesgue integrability on the root box. -/
theorem phaseError_integrableOn (F : EdgeSet (n+1)) (hm : 8 ≤ n+1)
    {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8) : IntegrableOn (phaseError F) (rootBoxSet n r) := by
  rw [← integrable_indicator_iff (rootBoxSet_measurable n r)]
  apply ((realKernel_integrable (rootMatrix_posDef F hm) 0).const_mul (errorBudget (n+1) r)).mono'
    ((phaseError_continuous F).measurable.indicator (rootBoxSet_measurable n r)).aestronglyMeasurable
  filter_upwards with x
  have hn : 0 ≤ (rootBoxSet n r).indicator (phaseError F) x := by
    apply indicator_nonneg _ x
    intro y _
    exact norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact indicator_phaseError_le F hr hrp x

/-- Integrating the actual local phase error costs only its Gaussian normalizer. -/
theorem phaseError_integral_bound (F : EdgeSet (n+1)) (hm : 8 ≤ n+1)
    {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8) :
    (∫ x in rootBoxSet n r, phaseError F x) ≤ errorBudget (n+1) r*normalization (rootMatrix F) := by
  rw [← integral_indicator (rootBoxSet_measurable n r)]
  have hi := (integrable_indicator_iff (rootBoxSet_measurable n r)).mpr (phaseError_integrableOn F hm hr hrp)
  have hk := (realKernel_integrable (rootMatrix_posDef F hm) 0).const_mul (errorBudget (n+1) r)
  refine (integral_mono hi hk (indicator_phaseError_le F hr hrp)).trans_eq ?_
  rw [integral_const_mul, zero_integral (rootMatrix_posDef F hm)]

theorem cutoff_phaseError_integral_bound (F : EdgeSet (n+1)) (hm : 8 ≤ n+1)
    (hc : cutoff (n+1) ≤ Real.pi/8) :
    (∫ x in rootBoxSet n (cutoff (n+1)), phaseError F x) / normalization (rootMatrix F) ≤ cutoffError (n+1) := by
  apply (div_le_iff₀ (normalization_pos (rootMatrix_posDef F hm))).mpr
  have h := phaseError_integral_bound F hm (cutoff_nonneg _) hc
  rwa [errorBudget_cutoff _ (by omega)] at h
/-- Uniform local integrated error along any sequence of actual finite edge sets. -/
theorem cutoff_phaseError_tendsto (F : ∀ n : ℕ, EdgeSet (n+1)) :
    Filter.Tendsto (fun n =>
      (∫ x in rootBoxSet n (cutoff (n+1)), phaseError (F n) x) / normalization (rootMatrix (F n)))
      Filter.atTop (𝓝 0) := by
  have hc := (Filter.tendsto_add_atTop_nat 1).eventually cutoff_eventually_quarter
  apply squeeze_zero' _ _ (cutoffError_tendsto.comp (Filter.tendsto_add_atTop_nat 1))
  · filter_upwards [Filter.eventually_ge_atTop 7] with n hn
    exact div_nonneg (integral_nonneg (fun _ => norm_nonneg _))
      (normalization_pos (rootMatrix_posDef (F n) (by omega))).le
  · filter_upwards [Filter.eventually_ge_atTop 7, hc] with n hn hc'
    exact cutoff_phaseError_integral_bound (F n) (by omega) hc'
end LocalLogCos
