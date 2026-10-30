module

public import TournamentHamiltonian.BlockRatio.Limit
public import TournamentHamiltonian.BlockRatio.UniformBridge

@[expose] public section

open Filter Topology
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- Genuine uniform edge weights, fixed actual base tournament, and the existing spectral constant. -/
theorem uniform_weight_ratio_tendsto {d : ℕ} (T : Tournament d)
    (hT : IsRegular T) (hd : 0 < d) :
    let D : (m : ℕ) → Matrix (Vertex d m) (Vertex d m) ℝ := fun m =>
      (2 / ((d * m : ℕ) - 1 : ℝ)) • UniformBlowup.weight T
    let B := fun m => D m - (1 / (d * m : ℕ) : ℝ) • ones (Vertex d m)
    Tendsto (fun m : ℕ => Matrix.det (1 - B m) * gramGaussian (B m)) atTop
      (𝓝 (Real.exp 1 * spectralRatio T)) := by
  dsimp only
  simp only [← weightMatrix_eq_uniform_weight]
  exact centered_det_gramGaussian_tendsto T hT hd

/-- The same actual-weight limit after the exact `Fin (d*m)` relabelling. -/
theorem uniform_weightFin_ratio_tendsto {d : ℕ} (T : Tournament d)
    (hT : IsRegular T) (hd : 0 < d) :
    let D : (m : ℕ) → Matrix (Fin (d * m)) (Fin (d * m)) ℝ := fun m =>
      Matrix.submatrix ((2 / ((d * m : ℕ) - 1 : ℝ)) •
        (UniformBlowup.weight T : Matrix (Vertex d m) (Vertex d m) ℝ))
          finProdFinEquiv.symm finProdFinEquiv.symm
    Tendsto (fun m : ℕ => Matrix.det (1 - (D m - averagingMatrix (Fin (d * m)))) *
      gramGaussian (D m - averagingMatrix (Fin (d * m)))) atTop
      (𝓝 (Real.exp 1 * spectralRatio T)) := by
  dsimp only
  simp only [← weightMatrix_eq_uniform_weight]
  exact densityFin_det_gramGaussian_tendsto T hT hd

end
end UniformBlockMatrix
