module

public import Mathlib.Analysis.SpecialFunctions.Stirling

@[expose] public section

set_option autoImplicit false
namespace NonregularNormalization
open Filter
open scoped Topology BigOperators
noncomputable section

/-- The first-order Robbins correction to the actual Stirling sequence. -/
def correctedStirling (k : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq (k+1)) - 1 / (12*((k+1 : ℕ) : ℝ))

theorem correctedStirling_monotone : Monotone correctedStirling := by
  apply monotone_nat_of_le_succ
  intro k
  have h := Stirling.log_stirlingSeq_sdiff_le (k+1)
  have he : (1 : ℝ)/(12*((k+1 : ℕ) : ℝ)) - 1/(12*((k+2 : ℕ) : ℝ)) =
      1/(12*((k+1 : ℕ) : ℝ)*(((k+1 : ℕ) : ℝ)+1)) := by
    push_cast
    field_simp
    ring
  dsimp [correctedStirling]
  have hk : k+1+1 = k+2 := by omega
  rw [hk] at h ⊢
  linarith

theorem correctedStirling_tendsto :
    Tendsto correctedStirling atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
  have hl := (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)).log
    (by positivity : Real.sqrt Real.pi ≠ 0)
  have hr : Tendsto (fun k : ℕ => (1 : ℝ)/(12*((k+1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).div_const (12 : ℝ)
    simpa only [Function.comp_def, zero_div, div_div, mul_comm] using h
  have h := hl.sub hr
  simp only [sub_zero] at h
  exact h

theorem log_stirlingSeq_le_robbins {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) ≤ Real.log (Real.sqrt Real.pi) + 1/(12*(n : ℝ)) := by
  have h := correctedStirling_monotone.ge_of_tendsto correctedStirling_tendsto (n-1)
  simp only [correctedStirling, Nat.sub_add_cancel hn] at h
  linarith

/-- Fine global upper bound with the precise 1/(12n) remainder required by §11.5. -/
theorem log_factorial_robbins_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ)*Real.log n - n + Real.log (2*Real.pi*n)/2 + 1/(12*(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := log_stirlingSeq_le_robbins hn
  rw [Stirling.log_stirlingSeq_formula] at h
  rw [Real.log_div hnR.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne',
    Real.log_sqrt Real.pi_pos.le] at h
  rw [Real.log_mul (by positivity : 2*Real.pi ≠ 0) hnR.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_pos.ne']
  linarith

/-- Matching global lower Stirling bound, in the same explicit normalization. -/
theorem log_factorial_stirling_lower (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ)*Real.log n - n + Real.log (2*Real.pi*n)/2 ≤ Real.log (n.factorial : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.log_mul (by positivity : 2*Real.pi ≠ 0) hnR.ne']
  have h := Stirling.le_log_factorial_stirling (by omega : n ≠ 0)
  linarith

end
end NonregularNormalization
