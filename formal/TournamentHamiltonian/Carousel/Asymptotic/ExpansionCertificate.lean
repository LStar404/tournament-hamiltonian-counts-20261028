module
public import TournamentHamiltonian.Carousel.Asymptotic.ActualExpansion

@[expose] public section
namespace TournamentHamiltonian
open Asymptotics Filter Topology

/-- The degree-five truncation appearing in the proved actual-carousel expansion. -/
noncomputable def carouselApproxPolynomial : Polynomial ℝ :=
  Polynomial.C 1 + Polynomial.monomial 2 carouselA2 + Polynomial.monomial 4 carouselA4 +
    Polynomial.monomial 5 (-1/3)

theorem carouselApproxPolynomial_eval (x : ℝ) :
    carouselApproxPolynomial.eval x = 1+carouselA2*x^2+carouselA4*x^4-x^5/3 := by
  simp only [carouselApproxPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_monomial]
  ring

/-- The vanishing orders are actual coefficients of the proved approximating polynomial. -/
theorem carouselApproxPolynomial_linear_cubic_zero :
    carouselApproxPolynomial.coeff 1=0 ∧ carouselApproxPolynomial.coeff 3=0 := by
  norm_num [carouselApproxPolynomial, Polynomial.coeff_add, Polynomial.coeff_monomial, Polynomial.coeff_one]

theorem carouselApproxPolynomial_nonzero_coefficients :
    carouselApproxPolynomial.coeff 0=1 ∧ carouselApproxPolynomial.coeff 2=carouselA2 ∧
      carouselApproxPolynomial.coeff 4=carouselA4 ∧ carouselApproxPolynomial.coeff 5=-1/3 := by
  norm_num [carouselApproxPolynomial, Polynomial.coeff_add, Polynomial.coeff_monomial, Polynomial.coeff_one]

/-- The coefficient certificate is tied to the actual tournament constants by a
sixth-order error, rather than being an isolated formal polynomial identity. -/
theorem regularCarouselConstant_polynomial_sixth_error :
    (fun m => regularCarouselConstant m/lowerConstant-
      carouselApproxPolynomial.eval (carouselScale m)) =O[atTop] (fun m => carouselScale m^6) := by
  simpa only [carouselApproxPolynomial_eval] using regularCarouselConstant_ratio_sixth_expansion

end TournamentHamiltonian
