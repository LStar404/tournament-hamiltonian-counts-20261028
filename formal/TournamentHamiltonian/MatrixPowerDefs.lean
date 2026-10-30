module

public import TournamentHamiltonian.ComparisonMatrix
public import TournamentHamiltonian.TransitiveDeterminant
public import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

/-- Squared Frobenius mass of an actual finite real matrix. -/
def matrixFrobSq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

theorem matrixFrobSq_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ matrixFrobSq A := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end TournamentHamiltonian
