module

public import TournamentHamiltonian.BlockMatrix.ScalarRatio

set_option autoImplicit false
@[expose] public section
open scoped Matrix.Norms.L2Operator
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- The limit's uncentered matrix ratio is exactly the original spectral ratio,
not a second independent definition of the tournament constant. -/
theorem rawRatio_normalized_sign_eq_spectralRatio {d : ℕ} (T : Tournament d) :
    rawRatio (((1 : ℝ) / d) • signMatrix T) = spectralRatio T := by
  have hn : Matrix.det (1 - ((1 : ℝ) / d) • signMatrix T) =
      Matrix.det (1 + ((1 : ℝ) / d) • signMatrix T) := by
    rw [← Matrix.det_transpose (1 - ((1 : ℝ) / d) • signMatrix T)]
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      signMatrix_transpose, smul_neg, sub_neg_eq_add]
  have hg : 1 - ((((1 : ℝ) / d) • signMatrix T).transpose *
      (((1 : ℝ) / d) • signMatrix T)) = skewGram T := by
    rw [Matrix.transpose_smul, smul_mul_assoc, Matrix.mul_smul, smul_smul]
    have hc : ((1 : ℝ) / d) * (1 / d) = 1 / (d : ℝ) ^ 2 := by ring
    rw [hc]
    rfl
  unfold rawRatio
  rw [hn, hg]
  unfold spectralRatio gaussianFactor
  ring

/-- In particular the denominator at the fixed-base limit matrix is strictly positive. -/
theorem normalized_sign_gram_det_pos {d : ℕ} (T : Tournament d) (hd : 0 < d) :
    0 < Matrix.det (1 - ((((1 : ℝ) / d) • signMatrix T).transpose *
      (((1 : ℝ) / d) • signMatrix T))) := by
  have hg : 1 - ((((1 : ℝ) / d) • signMatrix T).transpose *
      (((1 : ℝ) / d) • signMatrix T)) = skewGram T := by
    rw [Matrix.transpose_smul, smul_mul_assoc, Matrix.mul_smul, smul_smul]
    have hc : ((1 : ℝ) / d) * (1 / d) = 1 / (d : ℝ) ^ 2 := by ring
    rw [hc]
    rfl
  rw [hg]
  exact skewGram_det_pos T hd

end
end UniformBlockMatrix
