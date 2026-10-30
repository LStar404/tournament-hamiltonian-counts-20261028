module
public import TournamentHamiltonian.Carousel.CarouselConstants

@[expose] public section
namespace TournamentHamiltonian

/-- Exact first nontrivial carousel spectral ratio, not a numerical approximation. -/
theorem carousel_spectralRatio_order_three : spectralRatio (carouselTournament 1) = 2 := by
  apply Complex.ofReal_injective
  rw [carousel_spectralRatio_eq, transitiveRatio_eq_binomialMean]
  norm_num [binomialMean, pow_succ, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.normSq]

theorem carousel_spectralRatio_order_five : spectralRatio (carouselTournament 2) = 44/19 := by
  apply Complex.ofReal_injective
  rw [carousel_spectralRatio_eq, transitiveRatio_eq_binomialMean]
  norm_num [binomialMean, pow_succ, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.normSq]

theorem carousel_spectralRatio_order_seven : spectralRatio (carouselTournament 3) = 3032/1231 := by
  apply Complex.ofReal_injective
  rw [carousel_spectralRatio_eq, transitiveRatio_eq_binomialMean]
  norm_num [binomialMean, pow_succ, Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.normSq]

theorem regularCarouselConstant_order_three : regularCarouselConstant 1 = Real.exp (1/3) * 2 := by
  norm_num [regularCarouselConstant, carousel_spectralRatio_order_three]

theorem regularCarouselConstant_order_five : regularCarouselConstant 2 = Real.exp (1/5) * (44/19) := by
  norm_num [regularCarouselConstant, carousel_spectralRatio_order_five]

theorem regularCarouselConstant_order_seven : regularCarouselConstant 3 = Real.exp (1/7) * (3032/1231) := by
  norm_num [regularCarouselConstant, carousel_spectralRatio_order_seven]

end TournamentHamiltonian
