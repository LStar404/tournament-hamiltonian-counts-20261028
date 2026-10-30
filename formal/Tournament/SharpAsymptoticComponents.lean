module

public import Tournament.SharpBound
public import Tournament.ScorePenalty
public import TournamentHamiltonian.CarouselPathLower
public import TournamentHamiltonian.UniformSpectralUpper
public import TournamentHamiltonian.SharpSpectralMoments
public import TournamentHamiltonian.ComparisonMatrix
public import TournamentHamiltonian.SharpAssembly

/-!
# Unconditional components of the sharp Hamilton-path asymptotic

This entrance includes the actual carousel lower bound and the uniform
upper bound retaining the tournament-specific spectral factor. It does
not prove `SharpMainBound`: the sharp finite matrix-power comparison is
still missing. No spectral comparison is registered as an axiom.
-/

@[expose] public section

namespace TournamentPaths

theorem signMatrix_toLegacy {n : ℕ} (T : Tournament (Fin n)) :
    TournamentHamiltonian.signMatrix (toLegacy T) = signMatrix T := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [TournamentHamiltonian.signMatrix]
  · have h := T.oriented i j hij
    cases hi : T.edge i j <;> cases hj : T.edge j i <;>
      simp_all [TournamentHamiltonian.signMatrix, toLegacy, signMatrix, adjacency,
        Matrix.transpose_apply]

/-- The actual spectral factor of the current Boolean tournament. -/
noncomputable def pathSpectralRatio {n : ℕ} (T : Tournament (Fin n)) : ℝ :=
  TournamentHamiltonian.spectralRatio (toLegacy T)

/-- Quantitative lower bound for the current genuine finite maximum at both parities. -/
theorem maxPathCountFinite_lower_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (TournamentHamiltonian.lowerConstant - C / n) * TournamentHamiltonian.meanPaths n ≤
        (maxPathCountFinite n : ℝ) := by
  simpa only [maxPathCountFinite_eq_legacy] using TournamentHamiltonian.maxPaths_lower_uniform

/-- A single absolute error and threshold work for every current tournament. -/
theorem pathCountFinite_spectral_upper_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ T : Tournament (Fin n),
      (pathCountFinite T : ℝ) / TournamentHamiltonian.meanPaths n ≤ pathSpectralRatio T + C / n := by
  obtain ⟨C, hC, h⟩ := TournamentHamiltonian.actual_uniform_pathCount_spectral_upper
  refine ⟨C, hC, ?_⟩
  filter_upwards [h] with n hn T
  simpa only [pathCountFinite_eq_legacy, pathSpectralRatio] using hn (toLegacy T)

end TournamentPaths
