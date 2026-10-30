module

public import TournamentHamiltonian.ForestQuartic.Removed

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ForestQuartic
open MeasureTheory ProbabilityTheory GaussianQuartic ForestGaussian Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

def errorRate (m : ℕ) : ℝ := Real.exp 4 * (Real.sqrt (3/(m : ℝ)) + Real.sqrt 1680/(12*(m : ℝ)))
def expDeviation {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) : ℝ :=
  |Real.exp (-forestQuartic F z) - Real.exp (-(1/2 : ℝ))|

theorem forestQuartic_measurable {m : ℕ} (F : EdgeSet m) : Measurable (forestQuartic F) := by
  unfold forestQuartic edge4
  fun_prop

theorem deviation_integrable {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    Integrable (fun z => |forestQuartic F z-1/2|) (tiltedMeasure F) :=
  (memLp_tilt_integrable F hm ((forest_memLp F).sub (memLp_const _))).abs

theorem forest_concentration {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    (∫ z, |forestQuartic F z-1/2| ∂tiltedMeasure F) ≤ errorRate m := by
  have hpoint (z : Fin m → ℝ) : |forestQuartic F z-1/2| ≤ |quartic m z-1/2|+removedQuartic F z := by
    have h := forest_add_removed F z
    calc
      _ = |(quartic m z-1/2)-removedQuartic F z| := by congr 1; linarith
      _ ≤ |quartic m z-1/2|+|removedQuartic F z| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (removedQuartic_nonneg F z)]
  have hc : Integrable (fun z => |quartic m z-1/2|) (tiltedMeasure F) :=
    (memLp_tilt_integrable F hm ((quartic_memLp_two m).sub (memLp_const _))).abs
  calc
    _ ≤ ∫ z, |quartic m z-1/2|+removedQuartic F z ∂tiltedMeasure F :=
      integral_mono (deviation_integrable F hm) (hc.add (removed_tilt_integrable F hm)) hpoint
    _ = (∫ z, |quartic m z-1/2| ∂tiltedMeasure F) + ∫ z, removedQuartic F z ∂tiltedMeasure F :=
      integral_add hc (removed_tilt_integrable F hm)
    _ ≤ Real.exp 4*Real.sqrt (3/(m : ℝ))+Real.exp 4*Real.sqrt 1680/(12*(m : ℝ)) :=
      add_le_add (tilted_complete_concentration F hm) (removed_tilt_bound F hm)
    _ = errorRate m := by unfold errorRate; ring

theorem expDeviation_pointwise {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) :
    expDeviation F z ≤ |forestQuartic F z-1/2| :=
  exp_neg_lipschitz (forestQuartic_nonneg F z) (by norm_num)

theorem expDeviation_integrable {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    Integrable (expDeviation F) (tiltedMeasure F) := by
  have hmfun : Measurable (expDeviation F) := by
    have h := forestQuartic_measurable F
    unfold expDeviation
    fun_prop
  apply (deviation_integrable F hm).mono' hmfun.aestronglyMeasurable
  filter_upwards with z
  simpa only [Real.norm_eq_abs, expDeviation, abs_abs] using (expDeviation_pointwise F z)

theorem expDeviation_bound {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    (∫ z, expDeviation F z ∂tiltedMeasure F) ≤ errorRate m :=
  (integral_mono (expDeviation_integrable F hm) (deviation_integrable F hm)
    (expDeviation_pointwise F)).trans (forest_concentration F hm)

/-- The same estimate as an actual normalized Lebesgue K-kernel integral. -/
theorem volume_expDeviation_bound {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    (∫ z, kernelDensity F z * expDeviation F z) / PDGaussian.normalization (K F) ≤ errorRate m := by
  have h := expDeviation_bound F hm
  rw [tilted_integral_volume F (by omega)] at h
  simpa only [smul_eq_mul, div_eq_inv_mul] using h

theorem volume_expDeviation_integrable {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    Integrable (fun z => kernelDensity F z * expDeviation F z) := by
  exact (tilted_integrable_volume_iff F (by omega) _).mp (expDeviation_integrable F hm)

theorem errorRate_tendsto : Tendsto errorRate atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => Real.sqrt (3/(m : ℝ))) atTop (𝓝 0) := by
    have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3).sqrt
    simpa only [mul_zero, Real.sqrt_zero, mul_one_div] using h
  have h2 : Tendsto (fun m : ℕ => Real.sqrt 1680/(12*(m : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.sqrt 1680/12)
    have he : (fun m : ℕ => Real.sqrt 1680/(12*(m : ℝ))) =
        fun m : ℕ => (Real.sqrt 1680/12)*(1/(m : ℝ)) := by funext m; ring
    rw [he]
    simpa only [mul_zero] using h
  have h := (h1.add h2).const_mul (Real.exp 4)
  change Tendsto (fun m : ℕ => Real.exp 4*(Real.sqrt (3/(m : ℝ))+Real.sqrt 1680/(12*(m : ℝ)))) atTop (𝓝 0)
  simpa only [add_zero, mul_zero] using h

/-- Uniform in every sequence of genuine finite edge sets; dimensions change with m. -/
theorem forest_exp_L1_tendsto (F : ∀ m : ℕ, EdgeSet m) :
    Tendsto (fun m => ∫ z, expDeviation (F m) z ∂tiltedMeasure (F m)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun m => integral_nonneg (fun z => abs_nonneg _)))
    _ errorRate_tendsto
  filter_upwards [eventually_ge_atTop 16] with m hm
  exact expDeviation_bound (F m) hm
end ForestQuartic
