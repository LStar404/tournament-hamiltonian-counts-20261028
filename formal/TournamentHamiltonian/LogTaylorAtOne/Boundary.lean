module

public import TournamentHamiltonian.LogTaylorAtOne.Remainders

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace LogTaylorAtOne

theorem logCosh_remainder_at_center : logCoshRemainder 1 = 0 := by
  simp [logCoshRemainder]

theorem negLogCos_remainder_at_center : negLogCosRemainder 1 = 0 := by
  simp [negLogCosRemainder]

theorem hyperbolic_delta_zero :
    |Real.log (Real.cosh (1+(0:ℝ)))-Real.log (Real.cosh 1)-Real.tanh 1*0-
      (1-(Real.tanh 1)^2)*0^2/2| = 0 := by simp

theorem hyperbolic_delta_neg_one :
    |-Real.log (Real.cosh 1)+Real.tanh 1-(1-(Real.tanh 1)^2)/2| ≤ (1:ℝ)/3 := by
  have h := log_cosh_at_one_M_six (-1)
  norm_num at h
  linarith [h]

theorem hyperbolic_delta_one :
    |Real.log (Real.cosh 2)-Real.log (Real.cosh 1)-Real.tanh 1-
      (1-(Real.tanh 1)^2)/2| ≤ (1:ℝ)/3 := by
  have h := log_cosh_at_one_M_six 1
  norm_num at h ⊢
  exact h

theorem circular_alpha_zero :
    |Real.log (Real.cos 1)+Real.tan 1-(1+(Real.tan 1)^2)/2| ≤
      2*Real.tan 1/(Real.cos 1)^2/6 := by
  simpa using neg_log_cos_at_one_M_six (α:=0) (by norm_num) (by norm_num)

theorem circular_alpha_half :
    |negLogCosRemainder (1/2)| ≤ (2*Real.tan 1/(Real.cos 1)^2/6)/8 := by
  have h := negLogCos_remainder_bound (α:=1/2) (by norm_num)
  norm_num at h ⊢
  linarith

theorem third_logCosh_at_zero : iteratedDeriv 3 logCosh 0 = 0 := by
  rw [iteratedDeriv_logCosh 3 (by omega) 0]
  simp [hyperbolicJet]

theorem third_negLogCos_at_zero : iteratedDeriv 3 negLogCos 0 = 0 := by
  rw [third_negLogCos_eq (by simp : (0:ℝ) ∈ Set.Icc (0:ℝ) 1)]
  simp

theorem circular_coefficient_sec_factor :
    2*Real.tan 1/(Real.cos 1)^2/6 = Real.tan 1*(1+(Real.tan 1)^2)/3 := by
  rw [sec_sq_identity (cos_pos_on_unit (by simp : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)).ne']
  ring
end LogTaylorAtOne
