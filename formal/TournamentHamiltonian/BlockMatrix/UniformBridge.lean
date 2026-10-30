module

public import TournamentHamiltonian.BlockMatrix.Core
public import TournamentHamiltonian.UniformBlowup.Marginal

@[expose] public section

/-! Legacy bridge: the frozen `UniformBlowup` source predates Lean's `module` syntax.
The new matrix-analysis modules are public modules and do not depend on this bridge. -/
namespace UniformBlockMatrix
open TournamentHamiltonian
noncomputable section

/-- The block-algebra matrix is exactly the existing uniform model's entrywise weight. -/
theorem weightMatrix_eq_uniform_weight {d m : ℕ} (T : Tournament d) :
    weightMatrix (m := m) T = UniformBlowup.weight T := by
  ext u v
  rw [weightMatrix_apply]
  rfl

/-- Every algebraic matrix entry is the genuine finite-cube expectation. -/
theorem expected_arc_eq_weightMatrix {d m : ℕ} (T : Tournament d) (u v : Vertex d m) :
    (∑ ω : UniformBlowup.Sample d m,
      if UniformBlowup.arc T ω u v = true then (1 : ℝ) else 0) /
      Fintype.card (UniformBlowup.Sample d m) = weightMatrix T u v := by
  rw [weightMatrix_eq_uniform_weight]
  exact UniformBlowup.expected_arc_eq_weight T u v

end
end UniformBlockMatrix
