module

public import TournamentHamiltonian.LocalLogCos.Derivatives

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LocalLogCos
open Set Filter
open scoped Topology BigOperators Interval

def remainder (x : ℝ) : ℝ := logCos x+x^2/2+x^4/12

theorem taylor_five {x : ℝ} (hx : 0 ≠ x) :
    taylorWithinEval logCos 5 (uIcc 0 x) 0 x = -x^2/2-x^4/12 := by
  have hj (k : ℕ) (hk : k ≤ 6) : iteratedDerivWithin k logCos (uIcc 0 x) 0 = jet k 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx)
      (show ContDiffAt ℝ k logCos 0 from (Real.contDiff_cos.contDiffAt).log (by simp)) (by simp)]
    exact iteratedDeriv_logCos k hk (by simp)
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hj, jet, logCos]
  ring

theorem remainder_bounds_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi/4) :
    -x^6 ≤ remainder x ∧ remainder x ≤ 0 := by
  by_cases h0 : x=0
  · subst x
    norm_num [remainder, logCos]
  have hd : ContDiffOn ℝ (5+1) logCos (uIcc 0 x) := by
    apply Real.contDiff_cos.contDiffOn.log
    intro y hy
    apply (cos_pos_of_abs_le_quarter ?_).ne'
    rw [uIcc_of_le hx0] at hy
    rw [abs_of_nonneg hy.1]
    exact hy.2.trans hx
  obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm h0) hd
  have hy' : |y| ≤ Real.pi/4 := by
    rw [uIoo_of_le hx0] at hy
    rw [abs_of_pos hy.1]
    exact hy.2.le.trans hx
  have hb := sixth_derivative_bounds hy'
  rw [taylor_five (Ne.symm h0)] at he
  norm_num at he
  have hx6 : 0 ≤ x^6 := by positivity
  have hl := mul_le_mul_of_nonneg_right hb.1 hx6
  have hu := mul_nonpos_of_nonpos_of_nonneg hb.2 hx6
  unfold remainder
  constructor <;> nlinarith

theorem remainder_even (x : ℝ) : remainder (-x) = remainder x := by
  simp only [remainder, logCos, Real.cos_neg]
  ring

/-- Precise scalar quartic log-cosine remainder, with a genuine sixth-derivative proof. -/
theorem remainder_bounds {x : ℝ} (hx : |x| ≤ Real.pi/4) :
    -|x|^6 ≤ remainder x ∧ remainder x ≤ 0 := by
  rcases le_total 0 x with h | h
  · simpa only [abs_of_nonneg h] using remainder_bounds_nonneg h (by simpa only [abs_of_nonneg h] using hx)
  · have ha : -x ≤ Real.pi/4 := by simpa only [abs_of_nonpos h] using hx
    have hb := remainder_bounds_nonneg (neg_nonneg.mpr h) ha
    simpa only [abs_of_nonpos h, remainder_even] using hb

/-- Literal statement in the notation consumed by local product expansion. -/
theorem log_cos_quartic_bounds {x : ℝ} (hx : |x| ≤ Real.pi/4) :
    -|x|^6 ≤ Real.log (Real.cos x)+x^2/2+x^4/12 ∧
      Real.log (Real.cos x)+x^2/2+x^4/12 ≤ 0 :=
  remainder_bounds hx
end LocalLogCos
