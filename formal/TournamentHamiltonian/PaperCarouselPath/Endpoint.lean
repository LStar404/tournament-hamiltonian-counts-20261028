module

public import TournamentHamiltonian.UnitScorePathsApproximation
public import TournamentHamiltonian.SkewSpectrum

@[expose] public section

/-! The actual two carousel families in manuscript Corollary 8.2. -/
noncomputable section
namespace PaperCarouselPath
open TournamentHamiltonian

/-- One constant and one threshold, before both actual families and all indices.
This bounds their actual normalized Hamilton path counts, not `maxPaths`. -/
theorem carousel_pathCounts_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 20 ≤ N ∧ ∀ m : ℕ,
      (N ≤ 2 * m + 1 →
        |(pathCount (carouselTournament m) : ℝ) / meanPaths (2 * m + 1) - lowerConstant| ≤
          C / (2 * m + 1)) ∧
      (N ≤ 2 * m →
        |(pathCount (evenCarouselTournament m) : ℝ) / meanPaths (2 * m) - lowerConstant| ≤
          C / (2 * m)) := by
  obtain ⟨Np, hNp, hp⟩ := unit_score_pathCount_spectral_approximation_uniform
  obtain ⟨Cs, hCs, Ns, _hNs, hs⟩ := carousel_spectralRatios_error_bound
  refine ⟨unitScorePathApproximationConstant + Cs,
    add_pos_of_pos_of_nonneg unitScorePathApproximationConstant_pos hCs,
    max Np Ns, hNp.trans (le_max_left _ _), ?_⟩
  intro m
  constructor
  · intro hn
    have hp' := hp (2 * m + 1) (by omega) (carouselTournament m) (fun i => by
      rw [carouselTournament_score]; norm_num)
    have hs' := (hs m).1 (by omega)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hp'
    calc
      _ ≤ |(pathCount (carouselTournament m) : ℝ) / meanPaths (2 * m + 1) -
            spectralRatio (carouselTournament m)| +
          |spectralRatio (carouselTournament m) - lowerConstant| := abs_sub_le _ _ _
      _ ≤ unitScorePathApproximationConstant / (2 * m + 1) + Cs / (2 * m + 1) :=
        add_le_add hp' hs'
      _ = _ := (add_div _ _ _).symm
  · intro hn
    have hp' := hp (2 * m) (by omega) (evenCarouselTournament m)
      (fun i => (evenCarouselTournament_score m i).le)
    have hs' := (hs m).2 (by omega)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hp'
    calc
      _ ≤ |(pathCount (evenCarouselTournament m) : ℝ) / meanPaths (2 * m) -
            spectralRatio (evenCarouselTournament m)| +
          |spectralRatio (evenCarouselTournament m) - lowerConstant| := abs_sub_le _ _ _
      _ ≤ unitScorePathApproximationConstant / (2 * m) + Cs / (2 * m) :=
        add_le_add hp' hs'
      _ = _ := (add_div _ _ _).symm

/-- Corollary 8.2 with its original factorial mean and explicit limit constant. -/
theorem corollary8_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 20 ≤ N ∧ ∀ m : ℕ,
      (N ≤ 2 * m + 1 →
        |(pathCount (carouselTournament m) : ℝ) /
            (((2 * m + 1).factorial : ℝ) / 2 ^ (2 * m + 1 - 1)) -
          Real.cosh 1 / Real.cos 1| ≤ C / (2 * m + 1)) ∧
      (N ≤ 2 * m →
        |(pathCount (evenCarouselTournament m) : ℝ) /
            (((2 * m).factorial : ℝ) / 2 ^ (2 * m - 1)) -
          Real.cosh 1 / Real.cos 1| ≤ C / (2 * m)) := by
  simpa only [meanPaths, lowerConstant] using carousel_pathCounts_error_bound

end PaperCarouselPath
