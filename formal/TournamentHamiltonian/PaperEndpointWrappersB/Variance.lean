module

public import TournamentHamiltonian.StirlingNormalization

@[expose] public section

/-! Lemma 7.2 for all positive orders, including the two zero-permanent cases. -/
noncomputable section
namespace PaperEndpointWrappersB
open TournamentHamiltonian

/-- The literal variance-corrected bound with the concrete absolute constant exp(7). -/
theorem permanent_variance_all {n : ℕ} (T : Tournament n) (hn : 1 ≤ n) :
    (adjacency T).permanent ≤
      Real.exp 7 * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n *
        Real.exp (-degreeVariance T / (8 * (n : ℝ) ^ 2)) := by
  by_cases h3 : 3 ≤ n
  · exact adjacency_permanent_le_stirling_variance T h3
  · rw [adjacency_permanent_eq_zero_of_small_order T hn (by omega)]
    positivity

/-- Lemma 7.2's existential constant is now one compiled endpoint. -/
theorem lemma7_2 :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ T : Tournament n,
      (adjacency T).permanent ≤
        K * Real.sqrt ((n : ℝ) + 1) * (n.factorial : ℝ) / (2 : ℝ) ^ n *
          Real.exp (-degreeVariance T / (8 * (n : ℝ) ^ 2)) :=
  ⟨Real.exp 7, Real.exp_pos 7, fun _ hn T => permanent_variance_all T hn⟩

end PaperEndpointWrappersB
