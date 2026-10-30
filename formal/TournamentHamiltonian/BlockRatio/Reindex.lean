module

public import TournamentHamiltonian.BlockRatio.Decomposition
public import TournamentHamiltonian.BlockMatrix.DenseBridge

set_option autoImplicit false
@[expose] public section
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- The determinant ratio, like the norm, is invariant under an actual relabelling. -/
theorem rawRatio_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (Z : Matrix κ κ ℝ) (e : ι ≃ κ) :
    rawRatio (Z.submatrix e e) = rawRatio Z := by
  have hn : 1 - Z.submatrix e e = (1 - Z).submatrix e e := by
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv]
  have hg : 1 - (Z.submatrix e e).transpose * Z.submatrix e e =
      (1 - Z.transpose * Z).submatrix e e := by
    simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv,
      Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  rw [rawRatio, hn, hg, Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self]
  rfl

/-- Explicit centering compatibility with the dense-minor worker's matrix interface. -/
theorem densityFin_centered_eq {d m : ℕ} (T : Tournament d) :
    densityFin (m := m) T - averagingMatrix (Fin (d * m)) =
      (centered (m := m) T).submatrix finProdFinEquiv.symm finProdFinEquiv.symm := by
  ext i j
  simp [densityFin, centered, averagingMatrix, ones, one_div]

/-- Exact ratio factorization also holds for the actual `Fin (d*m)` dense matrix. -/
theorem densityFin_ratio_decomposition {d m : ℕ} (T : Tournament d)
    (hT : IsRegular T) (hN : 20 ≤ d * m) :
    Matrix.det (1 - (densityFin (m := m) T - averagingMatrix (Fin (d * m)))) *
      gramGaussian (densityFin (m := m) T - averagingMatrix (Fin (d * m))) =
      rawRatio (baseShift (m := m) T) * scalarRatio d m ^ (d * m - d) / scalarRatio d m := by
  rw [← rawRatio_eq_det_mul_gramGaussian, densityFin_centered_eq, rawRatio_submatrix_equiv]
  exact centered_rawRatio_decomposition T hT hN

end
end UniformBlockMatrix
