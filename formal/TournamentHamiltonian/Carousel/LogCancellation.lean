module

public import TournamentHamiltonian.Carousel.CarouselConstants
public import TournamentHamiltonian.SharpSpectralMoments

@[expose] public section

namespace TournamentHamiltonian
set_option backward.isDefEq.respectTransparency false

/-- The same exact determinant polynomial belongs to the actual transitive tournament. -/
theorem determinantRatio_transitiveTournament (n : ℕ) :
    determinantRatio (transitiveTournament n) = transitiveRatio n := by
  simp only [determinantRatio, complexSignMatrix_transitiveTournament,
    transitiveRatio, transitiveKernel]

/-- Signed similarity is reflected in the actual real spectral ratios. -/
theorem carousel_spectralRatio_eq_transitive (m : ℕ) :
    spectralRatio (carouselTournament m) = spectralRatio (transitiveTournament (2 * m + 1)) := by
  apply Complex.ofReal_injective
  rw [carousel_spectralRatio_eq, ← determinantRatio_eq_spectralRatio _ (by omega),
    determinantRatio_transitiveTournament]

theorem regularCarouselConstant_log (m : ℕ) :
    Real.log (regularCarouselConstant m) =
      1 / (2 * (m : ℝ) + 1) + Real.log (spectralRatio (transitiveTournament (2 * m + 1))) := by
  rw [regularCarouselConstant, Real.log_mul (Real.exp_pos _).ne'
    (spectralRatio_bounds _ (by omega)).1.ne', Real.log_exp,
    carousel_spectralRatio_eq_transitive]

/-- The first paired-mass moment is exactly the term canceled by the
regular-block exponential factor, at every odd order including one. -/
theorem transitive_pairedMasses_first_moment (m : ℕ) :
    2 * (pairedMasses (transitiveTournament (2 * m + 1))).sum =
      1 - 1 / (2 * (m : ℝ) + 1) := by
  rw [pairedMasses_sum _ (by omega)]
  push_cast
  field_simp

/-- The actual regular-carousel logarithm after exact cancellation of the first
moment. No Taylor expansion, asymptotic premise, or numerical fit is assumed. -/
theorem regularCarouselConstant_hasSum_log_tail (m : ℕ) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * (k + 1 : ℕ) + 1)) *
      ((pairedMasses (transitiveTournament (2 * m + 1))).map
        (fun x => x ^ (2 * (k + 1) + 1))).sum)
      (Real.log (regularCarouselConstant m) - 1) := by
  have hs := hasSum_log_ratio_product (pairedMasses (transitiveTournament (2 * m + 1)))
    (fun x hx => ⟨pairedMasses_nonneg _ x hx,
      (pairedMasses_lt_half _ (by omega) x hx).trans (by norm_num)⟩)
  rw [← spectralRatio_eq_paired_product _ (by omega)] at hs
  have ht := (hasSum_nat_add_iff' 1).mpr hs
  have hfirst := transitive_pairedMasses_first_moment m
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add,
    div_one, mul_one, pow_one, List.map_id'] at ht
  rw [hfirst] at ht
  convert ht using 1
  rw [regularCarouselConstant_log]
  ring

end TournamentHamiltonian
