module

public import TournamentHamiltonian.SubsetWeights

set_option autoImplicit false

@[expose] public section
namespace TournamentHamiltonian

/-- The needed reciprocal factorial bound is just one nonnegative Taylor term. -/
theorem dense_inverse_factorial_le_exp (n : ℕ) :
    (n : ℝ)^n / (n.factorial : ℝ) ≤ Real.exp n :=
  Real.pow_div_factorial_le_exp n (Nat.cast_nonneg n) n

/-- Large deletion converts the ambient exponential into a fixed exponential
in the deletion size; the base does not depend on `n`. -/
theorem dense_exp_ambient_le_geometric (δ : ℝ) (hδ : 0 < δ) (n k : ℕ)
    (hk : δ * (n : ℝ) ≤ k) :
    Real.exp n ≤ (Real.exp (1/δ))^k := by
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  rw [mul_one_div, le_div_iff₀ hδ]
  nlinarith

/-- Small deletion converts the quadratic logarithmic error to a fixed linear
exponential budget, retaining the harmless `k=0` correction. -/
theorem dense_small_log_budget (C δ : ℝ) (hC : 0 ≤ C) (_hδ : 0 ≤ δ)
    (n k : ℕ) (hn : 0 < n) (hk : (k : ℝ) ≤ δ*n) :
    C*((k : ℝ)+1)^2/n ≤ C + (4*C*δ)*(k : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hk0 : k = 0
  · subst k
    simp only [Nat.cast_zero, zero_add, one_pow, mul_one, mul_zero, add_zero]
    exact (div_le_self hC hn1)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk0)
  have hs : ((k : ℝ)+1)^2 ≤ 4*(k : ℝ)^2 := by nlinarith
  have hq : (k : ℝ)^2/n ≤ δ*k := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (Nat.cast_nonneg (α := ℝ) k)]
  calc
    _ ≤ C*(4*(k : ℝ)^2)/n := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs hC) hnR.le
    _ = (4*C)*((k : ℝ)^2/n) := by ring
    _ ≤ (4*C)*(δ*k) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ ≤ C + (4*C*δ)*(k : ℝ) := by nlinarith

/-- Scalar exponential control obtained from an actual positive ratio's log. -/
theorem dense_ratio_le_of_log_bound (r C δ : ℝ) (hr : 0 < r)
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (n k : ℕ) (hn : 0 < n)
    (hk : (k : ℝ) ≤ δ*n)
    (hlog : |Real.log r| ≤ C*((k : ℝ)+1)^2/n) :
    r ≤ Real.exp C * (Real.exp (4*C*δ))^k := by
  calc
    r = Real.exp (Real.log r) := (Real.exp_log hr).symm
    _ ≤ Real.exp (C + (4*C*δ)*(k : ℝ)) := Real.exp_le_exp.mpr
      ((le_abs_self _).trans (hlog.trans (dense_small_log_budget C δ hC hδ n k hn hk)))
    _ = _ := by rw [Real.exp_add, mul_comm (4*C*δ), Real.exp_nat_mul]

end TournamentHamiltonian
