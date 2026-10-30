module

public import TournamentHamiltonian.BlockMatrix.Reindex
public import TournamentHamiltonian.DenseMinorBounds

set_option autoImplicit false
@[expose] public section
open scoped Matrix.Norms.L2Operator
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- The independent dense-minor worker's exact five-field interface. -/
theorem FixedDenseClass.toDenseStochastic {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : FixedDenseClass D) : DenseStochastic D where
  nonnegative := hD.nonneg
  row_sum := hD.row_sum
  column_sum := hD.col_sum
  density := by simpa only [Fintype.card_fin] using hD.entry_le
  gap := by
    have he : averagingMatrix (Fin n) = (1 / (Fintype.card (Fin n) : ℝ)) • ones (Fin n) := by
      ext i j
      simp [averagingMatrix, ones, one_div]
    rw [he]
    exact hD.gap

/-- The true uniform block density directly satisfies the actual dense-minor interface. -/
theorem densityFin_denseStochastic {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 20 ≤ d * m) : DenseStochastic (densityFin (m := m) T) :=
  (densityFin_mem_fixedDenseClass T hT hN).toDenseStochastic

end
end UniformBlockMatrix
