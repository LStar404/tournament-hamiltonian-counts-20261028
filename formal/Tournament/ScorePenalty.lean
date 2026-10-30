module

public import Tournament.AsymptoticTransfer
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

/-!
# Uniform absorption of the manuscript's score-sensitive error

This is the scalar step following (7.2), also used in section 12.3.
The expression `tau * sqrt tau` is the nonnegative-real form of `tau^(3/2)`.
The eventual threshold is uniform in the whole interval `0 <= tau <= A log n`.
This module does not assume or establish (7.2) for Hamilton path counts.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Tournament

/-- The full exponent in manuscript (7.2), retaining its score penalty. -/
noncomputable def scorePenaltyExponent (K tau n : ℝ) : ℝ :=
  -tau + K * ((1 + tau + tau ^ 2) / n +
    (tau * Real.sqrt tau + tau) / Real.sqrt n + Real.sqrt (tau / n))

/-- A finite window bound; no limiting assumption is hidden in this statement. -/
theorem score_penalty_absorption_on_window (K tau T n : ℝ)
    (hK : 0 ≤ K) (htau : 0 ≤ tau) (htauT : tau ≤ T) (hn : 0 < n)
    (hwindow : K * ((1 + T) / n + (Real.sqrt T + 1) / Real.sqrt n) ≤ 1 / 4) :
    scorePenaltyExponent K tau n ≤ -tau / 2 + (K + K ^ 2) / n := by
  have hroot : Real.sqrt tau ≤ Real.sqrt T := Real.sqrt_le_sqrt htauT
  have hfirst : (1 + tau) / n ≤ (1 + T) / n :=
    div_le_div_of_nonneg_right (by linarith) hn.le
  have hsecond : (Real.sqrt tau + 1) / Real.sqrt n ≤
      (Real.sqrt T + 1) / Real.sqrt n :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg n)
  have hbudget : K * ((1 + tau) / n +
      (Real.sqrt tau + 1) / Real.sqrt n) ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hK).trans hwindow
  have hpoly : K * ((tau + tau ^ 2) / n +
      (tau * Real.sqrt tau + tau) / Real.sqrt n) ≤ tau / 4 := by
    convert mul_le_mul_of_nonneg_right hbudget htau using 1 <;> ring
  have hyoung := sqrt_error_absorption K tau n htau hn
  unfold scorePenaltyExponent
  have heq : K * ((1 + tau + tau ^ 2) / n +
      (tau * Real.sqrt tau + tau) / Real.sqrt n + Real.sqrt (tau / n)) =
      K / n + K * ((tau + tau ^ 2) / n +
      (tau * Real.sqrt tau + tau) / Real.sqrt n) + K * Real.sqrt (tau / n) := by ring
  rw [heq]
  calc
    _ ≤ -tau + (K / n + tau / 4 + (tau / 4 + K ^ 2 / n)) := by
      linarith only [hpoly, hyoung]
    _ = _ := by ring

/-- The complete coefficient budget tends to zero on the logarithmic window. -/
theorem score_window_budget_tendsto_zero (A K : ℝ) (hA : 0 ≤ A) :
    Tendsto (fun n : ℕ => K * ((1 + A * Real.log (n : ℝ)) / n +
      (Real.sqrt (A * Real.log (n : ℝ)) + 1) / Real.sqrt (n : ℝ))) atTop (𝓝 0) := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hinv := tendsto_inv_atTop_zero.comp hnat
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hfirst := hinv.add (hlog.const_mul A)
  have hsecond := ((hlog.const_mul A).sqrt).add hinv.sqrt
  have h := (hfirst.add hsecond).const_mul K
  simp only [mul_zero, Real.sqrt_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  simp only [Function.comp_apply, id_eq]
  have hsqrt : Real.sqrt (A * (Real.log (n : ℝ) / n)) =
      Real.sqrt (A * Real.log (n : ℝ)) / Real.sqrt (n : ℝ) := by
    rw [← mul_div_assoc, Real.sqrt_div (mul_nonneg hA hlog0)]
  rw [hsqrt, Real.sqrt_inv]
  ring

/-- A single threshold controls every score in the logarithmic window. -/
theorem score_penalty_absorption_uniform (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ A * Real.log (n : ℝ) →
      scorePenaltyExponent K tau n ≤ -tau / 2 + (K + K ^ 2) / n := by
  have h := (score_window_budget_tendsto_zero A K hA).eventually_le_const
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hn1 tau htau htauA
  exact score_penalty_absorption_on_window K tau (A * Real.log (n : ℝ)) n
    hK htau htauA (by exact_mod_cast (show 0 < n by omega)) hn

/-- Exponentiation preserves the useful negative half-score term. -/
theorem score_penalty_factor_uniform (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ A * Real.log (n : ℝ) →
      Real.exp (scorePenaltyExponent K tau n) ≤
        Real.exp (-tau / 2) * Real.exp ((K + K ^ 2) / n) := by
  filter_upwards [score_penalty_absorption_uniform A K hA hK] with n hn tau htau hwindow
  simpa only [Real.exp_add] using Real.exp_le_exp.mpr (hn tau htau hwindow)

/-- The score-dependent factor has an absolute uniform O(1/n) upper error. -/
theorem score_penalty_factor_le_one_add_uniform (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∀ᶠ n : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ A * Real.log (n : ℝ) →
      Real.exp (scorePenaltyExponent K tau n) ≤
        1 + ((K + K ^ 2) * Real.exp (K + K ^ 2)) / n := by
  filter_upwards [score_penalty_absorption_uniform A K hA hK,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1 tau htau hwindow
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : 0 ≤ K + K ^ 2 := by positivity
  have he : scorePenaltyExponent K tau n ≤ (K + K ^ 2) / n := by
    linarith [hn tau htau hwindow]
  have hfirst : Real.exp ((K + K ^ 2) / n) - 1 ≤
      ((K + K ^ 2) / n) * Real.exp ((K + K ^ 2) / n) := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-((K + K ^ 2) / n)))
      (Real.exp_nonneg ((K + K ^ 2) / n))
    have heq : Real.exp (-((K + K ^ 2) / n)) * Real.exp ((K + K ^ 2) / n) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [heq] at h
    nlinarith
  have hsecond := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (div_le_self hc hnR)) (div_nonneg hc hn0.le)
  have hexp := Real.exp_le_exp.mpr he
  have halg : (K + K ^ 2) / (n : ℝ) * Real.exp (K + K ^ 2) =
      ((K + K ^ 2) * Real.exp (K + K ^ 2)) / n := by ring
  rw [halg] at hsecond
  linarith

end Tournament
