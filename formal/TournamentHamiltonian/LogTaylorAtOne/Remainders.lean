module

public import TournamentHamiltonian.LogTaylorAtOne.Bounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LogTaylorAtOne
open Set Filter
open scoped Topology BigOperators Interval

def logCoshRemainder (x : ℝ) : ℝ :=
  logCosh x-logCosh 1-Real.tanh 1*(x-1)-(1-(Real.tanh 1)^2)*(x-1)^2/2

def negLogCosRemainder (x : ℝ) : ℝ :=
  negLogCos x-negLogCos 1-Real.tan 1*(x-1)-(1+(Real.tan 1)^2)*(x-1)^2/2

theorem logCosh_taylor_two {x : ℝ} (hx : 1 ≠ x) :
    taylorWithinEval logCosh 2 (uIcc 1 x) 1 x =
      logCosh 1+Real.tanh 1*(x-1)+(1-(Real.tanh 1)^2)*(x-1)^2/2 := by
  have hj (k : ℕ) (hk : k ≤ 3) : iteratedDerivWithin k logCosh (uIcc 1 x) 1 = hyperbolicJet k 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
      (show ContDiffAt ℝ k logCosh 1 from Real.contDiff_cosh.contDiffAt.log (Real.cosh_pos 1).ne') (by simp)]
    exact iteratedDeriv_logCosh k hk 1
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hj, hyperbolicJet]
  ring

theorem negLogCos_taylor_two {x : ℝ} (hx : 1 ≠ x) :
    taylorWithinEval negLogCos 2 (uIcc 1 x) 1 x =
      negLogCos 1+Real.tan 1*(x-1)+(1+(Real.tan 1)^2)*(x-1)^2/2 := by
  have hc := (cos_pos_on_unit (by simp : (1:ℝ) ∈ Icc (0:ℝ) 1)).ne'
  have hj (k : ℕ) (hk : k ≤ 3) : iteratedDerivWithin k negLogCos (uIcc 1 x) 1 = circularJet k 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
      (show ContDiffAt ℝ k negLogCos 1 from (Real.contDiff_cos.contDiffAt.log hc).neg) (by simp)]
    exact iteratedDeriv_negLogCos k hk hc
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hj, circularJet]
  ring

/-- The first printed M/6 estimate: the actual logarithmic hyperbolic remainder at one. -/
theorem logCosh_remainder_bound (x : ℝ) :
    |logCoshRemainder x| ≤ (2/6:ℝ)*|x-1|^3 := by
  by_cases hx : x=1
  · subst x; simp [logCoshRemainder]
  have hd : ContDiffOn ℝ (2+1) logCosh (uIcc 1 x) := by
    apply Real.contDiff_cosh.contDiffOn.log
    intro y _
    exact (Real.cosh_pos y).ne'
  obtain ⟨y,_,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm hx) hd
  rw [logCosh_taylor_two (Ne.symm hx)] at he
  have he' : logCoshRemainder x = iteratedDeriv 3 logCosh y*(x-1)^3/6 := by
    norm_num at he
    unfold logCoshRemainder
    linarith
  rw [he', abs_div, abs_mul, abs_pow]
  rw [abs_of_pos (by norm_num : (0:ℝ)<6)]
  have h := mul_le_mul_of_nonneg_right (third_logCosh_abs_le y) (pow_nonneg (abs_nonneg (x-1)) 3)
  nlinarith

/-- The second printed M/6 estimate, only on the original segment 0≤α≤1. -/
theorem negLogCos_remainder_bound {α : ℝ} (hα : α ∈ Icc (0:ℝ) 1) :
    |negLogCosRemainder α| ≤ (2*Real.tan 1/(Real.cos 1)^2/6)*|α-1|^3 := by
  by_cases hx : α=1
  · subst α; simp [negLogCosRemainder]
  have hd : ContDiffOn ℝ (2+1) negLogCos (uIcc 1 α) := by
    apply (Real.contDiff_cos.contDiffOn.log ?_).neg
    intro y hy
    apply (cos_pos_on_unit ?_).ne'
    rw [uIcc_of_ge hα.2] at hy
    exact ⟨hα.1.trans hy.1,hy.2⟩
  obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm hx) hd
  have hy' : y ∈ Icc (0:ℝ) 1 := by
    rw [uIoo_of_ge hα.2] at hy
    exact ⟨hα.1.trans hy.1.le,hy.2.le⟩
  rw [negLogCos_taylor_two (Ne.symm hx)] at he
  have he' : negLogCosRemainder α = iteratedDeriv 3 negLogCos y*(α-1)^3/6 := by
    norm_num at he
    unfold negLogCosRemainder
    linarith
  rw [he', abs_div, abs_mul, abs_pow]
  rw [abs_of_pos (by norm_num : (0:ℝ)<6)]
  have h := mul_le_mul_of_nonneg_right (third_negLogCos_abs_le hy') (pow_nonneg (abs_nonneg (α-1)) 3)
  nlinarith

/-- Literal delta notation used in §10.4; no restriction on delta is necessary. -/
theorem log_cosh_at_one_M_six (δ : ℝ) :
    |Real.log (Real.cosh (1+δ))-Real.log (Real.cosh 1)-Real.tanh 1*δ-
      (1-(Real.tanh 1)^2)*δ^2/2| ≤ (2/6:ℝ)*|δ|^3 := by
  simpa only [logCoshRemainder, logCosh, add_sub_cancel_left] using logCosh_remainder_bound (1+δ)

/-- Literal alpha notation and original closed interval; sec²(1) is written 1/cos²(1). -/
theorem neg_log_cos_at_one_M_six {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    |-Real.log (Real.cos α)+Real.log (Real.cos 1)-Real.tan 1*(α-1)-
      (1+(Real.tan 1)^2)*(α-1)^2/2| ≤ (2*Real.tan 1/(Real.cos 1)^2/6)*|α-1|^3 := by
  simpa only [negLogCosRemainder, negLogCos, sub_neg_eq_add] using negLogCos_remainder_bound ⟨hα0,hα1⟩
end LogTaylorAtOne
