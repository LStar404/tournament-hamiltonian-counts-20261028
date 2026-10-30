module

public import TournamentHamiltonian.BlockMatrix.UniformBridge
public import TournamentHamiltonian.BlockMatrix.DenseBridge

@[expose] public section

/-! End-to-end membership for the frozen model's actual weight, not just an equal surrogate. -/
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- Direct matrix-class statement about the existing uniform model's actual edge weights. -/
theorem uniform_density_mem_fixedDenseClass {d m : ℕ} (T : Tournament d)
    (hT : IsRegular T) (hN : 20 ≤ d * m) :
    FixedDenseClass ((2 / ((d * m : ℕ) - 1 : ℝ)) •
      (UniformBlowup.weight T : Matrix (Vertex d m) (Vertex d m) ℝ)) := by
  rw [← weightMatrix_eq_uniform_weight]
  exact density_mem_fixedDenseClass T hT hN

/-- Direct compatibility with the independent dense-minor worker after actual vertex relabelling. -/
theorem uniform_densityFin_denseStochastic {d m : ℕ} (T : Tournament d)
    (hT : IsRegular T) (hN : 20 ≤ d * m) :
    DenseStochastic (Matrix.submatrix ((2 / ((d * m : ℕ) - 1 : ℝ)) •
      (UniformBlowup.weight T : Matrix (Vertex d m) (Vertex d m) ℝ))
        finProdFinEquiv.symm finProdFinEquiv.symm) := by
  rw [← weightMatrix_eq_uniform_weight]
  exact densityFin_denseStochastic T hT hN

end
end UniformBlockMatrix
