module

public import TournamentHamiltonian.SharpAssembly
public import TournamentHamiltonian.FrobeniusComparison

/-!
# Sharp quantitative Hamilton-path asymptotic

The finite odd-moment comparison is proved from real skew-matrix bounds.
The final theorem has no permanent, scaling, moment-comparison, regularity,
or parity premise. Both its maximum and its counts are actual finite ones.
-/

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

theorem sharpMainBound : SharpMainBound := by
  apply sharpMainBound_of_odd_paired_moments
  intro n hn T k
  exact pairedMasses_odd_pow_sum_le_alternating T (by omega) k

/-- The literal constants and normalization of manuscript Theorem 1.1. -/
theorem sharp_path_asymptotic :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (Real.cosh 1 / Real.cos 1 - K / n) * ((n.factorial : ℝ) / 2 ^ (n - 1)) ≤
        (maxPaths n : ℝ) ∧
      (maxPaths n : ℝ) ≤
        (Real.cosh 1 / Real.cos 1 + K / n) * ((n.factorial : ℝ) / 2 ^ (n - 1)) := by
  simpa only [SharpMainBound, lowerConstant, meanPaths] using sharpMainBound

theorem sharp_path_normalized_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      |(maxPaths n : ℝ) / meanPaths n - Real.cosh 1 / Real.cos 1| ≤ K / n := by
  simpa only [lowerConstant] using sharpMainBound_iff_normalized_error.mp sharpMainBound

end TournamentHamiltonian

namespace TournamentPaths

/-- The same unconditional endpoint for the current tournament structure
and its genuine vertex-ordering maximum. -/
theorem sharp_path_count_maximum_asymptotic :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      |(maxPathCountFinite n : ℝ) / TournamentHamiltonian.meanPaths n -
        Real.cosh 1 / Real.cos 1| ≤ K / n := by
  simpa only [maxPathCountFinite_eq_legacy] using
    TournamentHamiltonian.sharp_path_normalized_error

end TournamentPaths
