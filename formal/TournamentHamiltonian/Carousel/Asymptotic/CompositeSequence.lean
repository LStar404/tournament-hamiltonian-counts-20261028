module
public import TournamentHamiltonian.Carousel.Asymptotic.SequenceBounds

@[expose] public section
namespace TournamentHamiltonian
open Asymptotics Filter Topology
set_option backward.isDefEq.respectTransparency false

/-- The algebraic composition step; all its hypotheses are discharged for the
actual alpha/beta and actual trigonometric functions below. -/
theorem quadratic_composition_sixth {f : ℕ → ℝ} {F : ℝ → ℝ} (a c₀ c₁ c₂ : ℝ)
    (hf : (fun m => f m-(1+a*carouselScale m^2+carouselScale m^4/5)) =O[atTop]
      (fun m => carouselScale m^6))
    (hF : (fun y => F y-(c₀+c₁*(y-1)+c₂*(y-1)^2)) =O[𝓝 1] (fun y => (y-1)^3)) :
    (fun m => F (f m)-(c₀+c₁*a*carouselScale m^2+
      (c₁/5+c₂*a^2)*carouselScale m^4)) =O[atTop] (fun m => carouselScale m^6) := by
  have hf4 := delta_fourth_bound a hf
  have hf2 := delta_second_bound a hf4
  have hft := delta_tendsto_one hf2
  have hcube : (fun m => (f m-1)^3) =O[atTop] (fun m => carouselScale m^6) := by
    simpa only [← pow_mul] using hf2.pow 3
  have ht := (hF.comp_tendsto hft).trans hcube
  have hsquare := delta_square_sixth_bound a hf4
  have h := (ht.add (hf.const_mul_left c₁)).add (hsquare.const_mul_left c₂)
  convert h using 1
  funext m
  simp only [Function.comp_def]
  ring

/-- Actual hyperbolic numerator through order four, with sixth-order remainder. -/
theorem carouselCoshBeta_sixth_remainder :
    (fun m => Real.cosh (carouselBeta (carouselScale m)) -
      (Real.cosh 1+Real.sinh 1/3*carouselScale m^2+
        (Real.sinh 1/5+Real.cosh 1/18)*carouselScale m^4)) =O[atTop]
      (fun m => carouselScale m^6) := by
  have hb : (fun m => carouselBeta (carouselScale m)-
      (1+(1/3 : ℝ)*carouselScale m^2+carouselScale m^4/5)) =O[atTop]
      (fun m => carouselScale m^6) := by
    convert carouselBeta_error_isBigO using 1
    funext m
    ring
  have h := quadratic_composition_sixth (f := fun m => carouselBeta (carouselScale m))
    (F := Real.cosh) (1/3) (Real.cosh 1) (Real.sinh 1) (Real.cosh 1/2) hb
    cosh_one_quadratic_remainder
  convert h using 1
  funext m
  ring

/-- Actual cosine denominator through order four, with sixth-order remainder. -/
theorem carouselCosAlpha_sixth_remainder :
    (fun m => Real.cos (carouselAlpha (carouselScale m)) -
      (Real.cos 1+Real.sin 1/3*carouselScale m^2-
        (Real.sin 1/5+Real.cos 1/18)*carouselScale m^4)) =O[atTop]
      (fun m => carouselScale m^6) := by
  have ha : (fun m => carouselAlpha (carouselScale m)-
      (1+(-1/3 : ℝ)*carouselScale m^2+carouselScale m^4/5)) =O[atTop]
      (fun m => carouselScale m^6) := by
    convert carouselAlpha_error_isBigO using 1
    funext m
    ring
  have hc : (fun y => Real.cos y-(Real.cos 1+(-Real.sin 1)*(y-1)+
      (-Real.cos 1/2)*(y-1)^2)) =O[𝓝 1] (fun y => (y-1)^3) := by
    convert cos_one_quadratic_remainder using 1
    funext y
    ring
  have h := quadratic_composition_sixth (f := fun m => carouselAlpha (carouselScale m))
    (F := Real.cos) (-1/3) (Real.cos 1) (-Real.sin 1) (-Real.cos 1/2) ha hc
  convert h using 1
  funext m
  ring

/-- Actual common exponential factor through degree five, with sixth-order remainder. -/
theorem carouselExpP_sixth_remainder :
    (fun m => Real.exp (carouselP (carouselScale m))-(1-carouselScale m^5/3)) =O[atTop]
      (fun m => carouselScale m^6) := by
  have hp5 : (fun m => carouselP (carouselScale m)) =O[atTop] (fun m => carouselScale m^5) := by
    have h := (carouselP_error_isBigO.trans (carouselScale_pow_isBigO (by omega : 5 ≤ 9))).sub
      ((isBigO_refl (fun m => carouselScale m^5) atTop).const_mul_left (1/3))
    convert h using 1
    funext m
    ring
  have hpt : Tendsto (fun m => carouselP (carouselScale m)) atTop (𝓝 0) :=
    hp5.trans_tendsto (by simpa using carouselScale_tendsto.pow 5)
  have hpsq : (fun m => carouselP (carouselScale m)^2) =O[atTop]
      (fun m => carouselScale m^10) := by
    simpa only [← pow_mul] using hp5.pow 2
  have he := (exp_zero_linear_remainder.comp_tendsto hpt).trans
    (hpsq.trans (carouselScale_pow_isBigO (by omega : 6 ≤ 10)))
  have hp6 := carouselP_error_isBigO.trans (carouselScale_pow_isBigO (by omega : 6 ≤ 9))
  convert he.add hp6 using 1
  funext m
  simp only [Function.comp_def]
  ring

end TournamentHamiltonian
