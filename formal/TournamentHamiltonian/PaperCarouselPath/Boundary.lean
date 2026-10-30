module

public import TournamentHamiltonian.PaperCarouselPath.Endpoint

@[expose] public section

/-! Actual-object and denominator guard checks. -/
noncomputable section
namespace PaperCarouselPath
open TournamentHamiltonian

theorem actual_odd_scores (m : ℕ) : ∀ i, score (carouselTournament m) i = 0 :=
  carouselTournament_score m

theorem actual_even_scores (m : ℕ) : ∀ i, |score (evenCarouselTournament m) i| = 1 :=
  evenCarouselTournament_score m

/-- The even family is the restriction of the specified odd family, not a chosen witness. -/
theorem actual_even_deletion (m : ℕ) (i j : Fin (2 * m)) :
    (evenCarouselTournament m).val i j =
      (carouselTournament m).val (carouselDeletionMap m i) (carouselDeletionMap m j) := rfl

/-- That restriction misses exactly one actual vertex. -/
theorem actual_deletion_range (m : ℕ) :
    Set.range (carouselDeletionMap m) =
      {v | v ≠ (carouselOrder m).symm (Fin.last (2 * m))} :=
  carouselDeletionMap_range m

theorem common_threshold_guard {N m : ℕ} (hN : 20 ≤ N) :
    (N ≤ 2 * m → 0 < 2 * m) ∧
    (N ≤ 2 * m + 1 → 0 < 2 * m + 1) ∧ ¬ N ≤ 0 ∧ ¬ N ≤ 1 := by omega

example (m : ℕ) : 0 < meanPaths (2 * m + 1) := by unfold meanPaths; positivity
example (m : ℕ) : 0 < meanPaths (2 * m) := by unfold meanPaths; positivity

end PaperCarouselPath
