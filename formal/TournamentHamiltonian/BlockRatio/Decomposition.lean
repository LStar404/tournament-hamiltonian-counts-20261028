module

public import TournamentHamiltonian.BlockRatio.Numerator
public import TournamentHamiltonian.BlockRatio.Denominator
public import TournamentHamiltonian.BlockRatio.SpectralBridge

set_option autoImplicit false
@[expose] public section
open scoped Matrix.Norms.L2Operator
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- The uncentered ratio is the existing Gram-Gaussian factor times its determinant. -/
theorem rawRatio_eq_det_mul_gramGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : Matrix ι ι ℝ) : rawRatio Z = Matrix.det (1 - Z) * gramGaussian Z := by
  simp only [rawRatio, gramGaussian, div_eq_mul_inv]

/-- Exact ratio factorization for the genuine uniform-block centered density.
The natural exponent is `N-d`; the extra constant direction is removed by division by `t`.
No negative natural exponent is used, including at `m=1`. -/
theorem centered_rawRatio_decomposition {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 20 ≤ d * m) :
    rawRatio (centered (m := m) T) = rawRatio (baseShift (m := m) T) *
      scalarRatio d m ^ (d * m - d) / scalarRatio d m := by
  have ha : 0 < 1 + blockStep d m := by
    linarith [blockStep_pos (by omega : 2 ≤ d * m)]
  have hb := scalar_sqrt_pos (by omega : 3 ≤ d * m)
  have hc := baseShift_gram_sqrt_pos T hN
  unfold rawRatio
  rw [centered_numerator_det T hT hN, centered_gram_sqrt T hT hN]
  simp only [scalarRatio, div_pow]
  field_simp

/-- Same exact theorem using the original permanent-analysis Gaussian factor, not a new surrogate. -/
theorem centered_det_gramGaussian_decomposition {d m : ℕ} (T : Tournament d)
    (hT : IsRegular T) (hN : 20 ≤ d * m) :
    Matrix.det (1 - centered (m := m) T) * gramGaussian (centered (m := m) T) =
      rawRatio (baseShift (m := m) T) * scalarRatio d m ^ (d * m - d) / scalarRatio d m := by
  rw [← rawRatio_eq_det_mul_gramGaussian]
  exact centered_rawRatio_decomposition T hT hN

end
end UniformBlockMatrix
