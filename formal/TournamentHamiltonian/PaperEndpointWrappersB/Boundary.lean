module

public import TournamentHamiltonian.PaperEndpointWrappersB.SmallScore
public import TournamentHamiltonian.PaperEndpointWrappersB.MainBound
public import TournamentHamiltonian.PaperEndpointWrappersB.Variance

@[expose] public section

/-! Finite boundary checks for the three aggregation wrappers. -/
noncomputable section
namespace PaperEndpointWrappersB
open TournamentHamiltonian

/-- Neither of the analytic smallness conditions is left to the caller. -/
theorem delta_guards : 0 < smallScoreDelta ∧ smallScoreDelta ≤ 1 / 4 ∧
    smallScoreUniformLogConstant * smallScoreDelta ≤ 1 :=
  ⟨smallScoreDelta_pos, smallScoreDelta_le_quarter, logConstant_mul_smallScoreDelta_le_one⟩

/-- This is the ordinary supremum norm of the actual score vector. -/
theorem actual_score_envelope {n : ℕ} (T : Tournament n) :
    0 ≤ ‖score T‖ ∧ ∀ i, |score T i| ≤ ‖score T‖ :=
  ⟨norm_nonneg _, fun i => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (score T) i⟩

/-- Equal deletion cardinalities do not force the independently chosen sets to agree. -/
theorem independent_deletion_sets :
    ({0} : Finset (Fin 3)).card = 1 ∧ ({1} : Finset (Fin 3)).card = 1 ∧
      ({0} : Finset (Fin 3)) ≠ {1} := by decide

theorem order_one_permanent (T : Tournament 1) : (adjacency T).permanent = 0 :=
  adjacency_permanent_eq_zero_of_small_order T (by omega) (by omega)

theorem order_two_permanent (T : Tournament 2) : (adjacency T).permanent = 0 :=
  adjacency_permanent_eq_zero_of_small_order T (by omega) (by omega)

/-- Order zero is not silently covered by the zero-permanent argument. -/
theorem order_zero_permanent (T : Tournament 0) : (adjacency T).permanent = 1 := Matrix.permanent_isEmpty

example (T : Tournament 1) : (adjacency T).permanent ≤
    Real.exp 7 * Real.sqrt (1 + 1) * (1 : ℝ) / 2 *
      Real.exp (-degreeVariance T / 8) := by
  simpa using permanent_variance_all T (by omega)

example (T : Tournament 2) : (adjacency T).permanent ≤
    Real.exp 7 * Real.sqrt (2 + 1) * (2 : ℝ) / 2 ^ 2 *
      Real.exp (-degreeVariance T / (8 * 2 ^ 2)) := by
  simpa using permanent_variance_all T (by omega)

example : MainBound := mainBound

end PaperEndpointWrappersB
