module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public section

namespace UniformFinalScalars
open Filter Topology
noncomputable section

/-- The restored cycle normalization factor. Subtraction is in the reals. -/
def normalizationBase (n : ℕ) : ℝ := ((n : ℝ) - 1) / (n : ℝ)
def cyclePrefactor (n : ℕ) : ℝ := normalizationBase n ^ n
def pathPrefactor (n : ℕ) : ℝ := normalizationBase n ^ (n-1)

theorem normalizationBase_eq (n : ℕ) (hn : 0 < n) :
    normalizationBase n = 1 + (-1 : ℝ)/(n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold normalizationBase
  field_simp
  ring

theorem normalizationBase_tendsto :
    Tendsto normalizationBase atTop (𝓝 (1 : ℝ)) := by
  have h : Tendsto (fun n : ℕ => 1 - 1/(n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [normalizationBase_eq n (by omega)]
  ring

theorem cyclePrefactor_tendsto :
    Tendsto cyclePrefactor atTop (𝓝 (Real.exp (-1))) := by
  apply (Real.tendsto_one_add_div_pow_exp (-1)).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [cyclePrefactor, normalizationBase_eq n (by omega)]

theorem pathPrefactor_tendsto :
    Tendsto pathPrefactor atTop (𝓝 (Real.exp (-1))) := by
  have h := cyclePrefactor_tendsto.div normalizationBase_tendsto (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hb : normalizationBase n ≠ 0 := div_ne_zero (sub_ne_zero.mpr hn1.ne') hnR.ne'
  change cyclePrefactor n / normalizationBase n = pathPrefactor n
  simp only [pathPrefactor, cyclePrefactor, pow_sub₀ _ hb (show 1 ≤ n by omega),
    pow_one, div_eq_mul_inv]

theorem cyclePrefactor_mul_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun m : ℕ => cyclePrefactor (d*m)) atTop (𝓝 (Real.exp (-1))) :=
  cyclePrefactor_tendsto.comp (tendsto_id.const_mul_atTop' hd)

theorem pathPrefactor_mul_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun m : ℕ => pathPrefactor (d*m)) atTop (𝓝 (Real.exp (-1))) :=
  pathPrefactor_tendsto.comp (tendsto_id.const_mul_atTop' hd)

/-- Cancels exactly the `exp 1` in the established block-ratio limit. -/
theorem exp_neg_one_mul_exp_one (ρ : ℝ) : Real.exp (-1) * (Real.exp 1 * ρ) = ρ := by
  rw [← mul_assoc, ← Real.exp_add]
  norm_num

end
end UniformFinalScalars
