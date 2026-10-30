module

public import TournamentHamiltonian.BlockRatio.Gram

set_option autoImplicit false
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- Exact Gram determinant factorization. The sign of the skew square is positive
in the Gram complement because `Sᵀ=-S`; the constant correction is `+h² J/N`. -/
theorem centered_gram_det {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 20 ≤ d * m) :
    Matrix.det (1 - (centered (m := m) T).transpose * centered T) =
      (1 - blockStep d m ^ 2) ^ (d * m - d) *
        Matrix.det (1 - (baseShift (m := m) T).transpose * baseShift (m := m) T) /
        (1 - blockStep d m ^ 2) := by
  have hm : 1 ≤ m := by nlinarith
  have hNR : (20 : ℝ) ≤ (d * m : ℕ) := by exact_mod_cast hN
  have hN0 : ((d * m : ℕ) : ℝ) ≠ 0 := by linarith
  have hp := scalar_gram_pos (by omega : 3 ≤ d * m)
  rw [centered_gram_eq_block T hT (by omega),
    det_smul_one_add_blockLift _ hm _ hp.ne']
  have heq : (1 - blockStep d m ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) +
      (m : ℝ) • ((blockStep d m ^ 2 * (m : ℝ)) • (signMatrix T * signMatrix T) +
        (blockStep d m ^ 2 / (d * m : ℕ)) • ones (Fin d)) =
      (1 - (baseShift (m := m) T).transpose * baseShift (m := m) T) +
        ((m : ℝ) * blockStep d m ^ 2 / (d * m : ℕ)) • ones (Fin d) := by
    rw [baseShift_gram_eq]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [heq, det_add_smul_ones_of_row_sum _ _ (1 - blockStep d m ^ 2) hp.ne'
    (baseShift_gram_row_sum T hT)]
  have hc : 1 + ((m : ℝ) * blockStep d m ^ 2 / (d * m : ℕ)) *
      (Fintype.card (Fin d) : ℝ) / (1 - blockStep d m ^ 2) = 1 / (1 - blockStep d m ^ 2) := by
    simp only [Fintype.card_fin]
    have hmul : (m : ℝ) * d = (d * m : ℕ) := by push_cast; ring
    field_simp
    nlinarith
  rw [hc]
  ring

theorem sqrt_nat_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

/-- Positive square roots split with the exact same natural exponent, including `m=1`. -/
theorem centered_gram_sqrt {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 20 ≤ d * m) :
    Real.sqrt (Matrix.det (1 - (centered (m := m) T).transpose * centered T)) =
      Real.sqrt (1 - blockStep d m ^ 2) ^ (d * m - d) *
        Real.sqrt (Matrix.det (1 - (baseShift (m := m) T).transpose * baseShift (m := m) T)) /
        Real.sqrt (1 - blockStep d m ^ 2) := by
  rw [centered_gram_det T hT hN,
    Real.sqrt_div' _ (scalar_gram_pos (by omega : 3 ≤ d * m)).le,
    Real.sqrt_mul (pow_nonneg (scalar_gram_pos (by omega : 3 ≤ d * m)).le _),
    sqrt_nat_pow _ (scalar_gram_pos (by omega : 3 ≤ d * m)).le]

end
end UniformBlockMatrix
