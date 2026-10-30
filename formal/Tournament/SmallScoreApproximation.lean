module

public import Tournament.SharpAsymptoticComponents
public import TournamentHamiltonian.GeneralSmallScoreAsymptotic

@[expose] public section

open Filter
open scoped Topology

namespace TournamentPaths

/-- The actual score is the row sum of the manuscript's sign matrix. -/
theorem score_toLegacy {n : ℕ} (T : Tournament (Fin n)) (i : Fin n) :
    TournamentHamiltonian.score (toLegacy T) i = ∑ j, signMatrix T i j := by
  simp only [TournamentHamiltonian.score, signMatrix_toLegacy]

/-- Theorem 8.1 for genuine current Hamilton orderings, uniformly over every
nonnegative o(sqrt n) score envelope. No minor or variance assumptions remain. -/
theorem small_score_pathCountFinite_spectral_approximation_eventually
    (d : ℕ → ℝ) (hd0 : ∀ n, 0 ≤ d n)
    (hd : Tendsto (fun n => d n / Real.sqrt n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ T : Tournament (Fin n),
      (∀ i, |∑ j, signMatrix T i j| ≤ d n) →
      |(pathCountFinite T : ℝ) / TournamentHamiltonian.meanPaths n -
          pathSpectralRatio T| ≤
        TournamentHamiltonian.unitScorePathApproximationConstant * (d n + 1) ^ 2 / n := by
  filter_upwards [TournamentHamiltonian.small_score_pathCount_spectral_approximation_eventually
    d hd0 hd] with n hn T hs
  have hscore : ∀ i, |TournamentHamiltonian.score (toLegacy T) i| ≤ d n := by
    simpa only [score_toLegacy] using hs
  simpa only [pathCountFinite_eq_legacy, pathSpectralRatio] using hn (toLegacy T) hscore

/-- A single positive absolute constant is chosen before the score envelope.
Only the common threshold may depend on that envelope, not on the tournament. -/
theorem small_score_path_approximation_absolute_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ → ℝ,
      (∀ n, 0 ≤ d n) →
      Tendsto (fun n => d n / Real.sqrt n) atTop (𝓝 0) →
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ T : Tournament (Fin n),
        (∀ i, |∑ j, signMatrix T i j| ≤ d n) →
        |(pathCountFinite T : ℝ) / TournamentHamiltonian.meanPaths n -
            pathSpectralRatio T| ≤ C * (d n + 1) ^ 2 / n := by
  refine ⟨TournamentHamiltonian.unitScorePathApproximationConstant,
    TournamentHamiltonian.unitScorePathApproximationConstant_pos, ?_⟩
  intro d hd0 hd
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (small_score_pathCountFinite_spectral_approximation_eventually d hd0 hd)
  refine ⟨max N 2, le_max_right _ _, ?_⟩
  intro n hn T hs
  exact hN n ((le_max_left N 2).trans hn) T hs

end TournamentPaths
