module

public import TournamentHamiltonian.WeightedCycle.Core
public import TournamentHamiltonian.UniformBlowup.Cycle

@[expose] public section

/-! Bridge to the actual finite uniform-internal-block model, without changing
its cycle objects or its independence hypotheses. -/
namespace WeightedCycle
open TournamentHamiltonian
open scoped BigOperators Classical
noncomputable section

/-- The existing expected adjacency, merely viewed as a matrix. -/
abbrev uniformWeightMatrix {d m : ℕ} (T : Tournament d) :
    Matrix (UniformBlowup.Vertex d m) (UniformBlowup.Vertex d m) ℝ :=
  UniformBlowup.weight T

/-- The exact same successor permutations as the actual blow-up model. -/
theorem cyc_eq_uniform_weightedCycleSum {d m : ℕ} (hN : 2 ≤ d * m)
    (T : Tournament d) :
    cyc (UniformBlowup.weight (m := m) T) = UniformBlowup.weightedCycleSum (m := m) T := by
  have hcard : 2 ≤ Fintype.card (UniformBlowup.Vertex d m) := by simpa using hN
  unfold cyc UniformBlowup.weightedCycleSum UniformBlowup.cycleWeight
  simp_rw [singleFullCycle_iff_cycle_support hcard]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The convolution counts the genuine uniform-model cycle expectation.
The `N ≥ 3` threshold is inherited from the no-repeated-unordered-edge proof,
not hidden in the generic finite matrix identity. -/
theorem uniform_avgCycle_convolution {d m : ℕ} (hN : 3 ≤ d * m)
    (T : Tournament d) :
    (d * m : ℝ) * UniformBlowup.avgCycle (m := m) T =
      -(∑ U : Finset (UniformBlowup.Vertex d m), (U.card : ℝ) *
        ((-(uniformWeightMatrix (m := m) T)).submatrix
          (Subtype.val : U → UniformBlowup.Vertex d m) Subtype.val).det *
        ((uniformWeightMatrix (m := m) T).submatrix
          (Subtype.val : (Uᶜ : Finset (UniformBlowup.Vertex d m)) → UniformBlowup.Vertex d m)
          Subtype.val).permanent) := by
  rw [UniformBlowup.avgCycle_eq_weightedCycleSum hN,
    ← cyc_eq_uniform_weightedCycleSum (by omega)]
  simpa using convolution (UniformBlowup.weight (m := m) T)

end
end WeightedCycle
