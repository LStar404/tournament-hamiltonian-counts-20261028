module

public import TournamentHamiltonian.DenseMinorScalars

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace TournamentHamiltonian

/-- Applied only to the actual normalized permanent ratios below. -/
theorem dense_actual_relative_log (r e : ℝ) (he : e ≤ 1/2) (hr : |r-1| ≤ e) :
    0 < r ∧ |Real.log r| ≤ 2*e := by
  have hh : 1/2 ≤ r := by have h := (abs_le.mp hr).1; linarith
  exact ⟨by linarith, (abs_log_le_twice_sub_one r hh).trans
    (mul_le_mul_of_nonneg_left hr (by norm_num))⟩

/-- Exact scalar assembly of mass normalization, factorial normalization and
actual relative errors. No asymptotic estimate is an input to this identity. -/
theorem dense_permanent_log_identity (n M k : ℕ) (hdim : n = M+k)
    (hn : 0 < n) (hM : 0 < M) (H c pQ pD pY GD GY : ℝ)
    (hH : 0 < H) (hD : 0 < pD) (hY : 0 < pY) (hGD : 0 < GD) (hGY : 0 < GY)
    (hrestore : pQ = Real.exp (-c) * (H/M)^M * pY) :
    Real.log (pQ/pD) = -c +
      Real.log ((n:ℝ)^k * (M.factorial:ℝ)/(n.factorial:ℝ)) +
      (M:ℝ)*Real.log ((n:ℝ)*H/(M:ℝ)^2) + (Real.log GY-Real.log GD) +
      (Real.log (((M:ℝ)^M/(M.factorial:ℝ))*pY/GY) -
        Real.log (((n:ℝ)^n/(n.factorial:ℝ))*pD/GD)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hQ : 0 < pQ := by rw [hrestore]; positivity
  rw [Real.log_div hQ.ne' hD.ne', hrestore,
    Real.log_mul (by positivity) hY.ne',
    Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
    Real.log_pow, Real.log_div hH.ne' hMR.ne',
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul hnR.ne' hH.ne', Real.log_pow,
    Real.log_div (by positivity) hGY.ne',
    Real.log_mul (by positivity) hY.ne', Real.log_div (by positivity) (by positivity),
    Real.log_pow,
    Real.log_div (by positivity) hGD.ne',
    Real.log_mul (by positivity) hD.ne', Real.log_div (by positivity) (by positivity),
    Real.log_pow]
  have hd : (n:ℝ) = M+k := by exact_mod_cast hdim
  rw [hd]
  ring

/-- Common denominator packaging keeps the genuine C/N contribution at k=0. -/
theorem dense_ratio_budget (N k C A B L : ℝ) (hN : 0 < N) (hk : 0 ≤ k)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) (_hL : 0 ≤ L) :
    4096*L^2*k^2/N + 2*k^2/N + 8*k^2/N + C*k/N + (4*B+2*A)/N ≤
      (10+4096*L^2+C+4*B+2*A)*(k+1)^2/N := by
  simp only [← add_div]
  apply (div_le_div_iff_of_pos_right hN).mpr
  nlinarith [mul_nonneg hC (show 0 ≤ k^2+k+1 by positivity),
    mul_nonneg (show 0 ≤ 4096*L^2+10 by positivity) (show 0 ≤ 2*k+1 by positivity),
    mul_nonneg (show 0 ≤ 4*B+2*A by positivity) (show 0 ≤ k^2+2*k by positivity)]

end TournamentHamiltonian
