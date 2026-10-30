module

public import TournamentHamiltonian.BlockRatio.Decomposition
public import TournamentHamiltonian.BlockMatrix.UniformDenseBridge

@[expose] public section

namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- Section 7's exact ratio for the original uniform model's actual edge weights. -/
theorem uniform_weight_ratio_decomposition {d m : ℕ} (T : Tournament d)
    (hT : IsRegular T) (hN : 20 ≤ d * m) :
    let D : Matrix (Vertex d m) (Vertex d m) ℝ :=
      (2 / ((d * m : ℕ) - 1 : ℝ)) • UniformBlowup.weight T
    let B := D - (1 / (d * m : ℕ) : ℝ) • ones (Vertex d m)
    Matrix.det (1 - B) * gramGaussian B =
      rawRatio (baseShift (m := m) T) * scalarRatio d m ^ (d * m - d) / scalarRatio d m := by
  dsimp only
  rw [← weightMatrix_eq_uniform_weight]
  exact centered_det_gramGaussian_decomposition T hT hN

end
end UniformBlockMatrix
