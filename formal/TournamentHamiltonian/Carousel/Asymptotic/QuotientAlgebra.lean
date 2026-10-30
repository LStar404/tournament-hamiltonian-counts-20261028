module
public import TournamentHamiltonian.Carousel.Asymptotic.CompositeSequence

@[expose] public section
namespace TournamentHamiltonian
open Asymptotics Filter Topology
set_option backward.isDefEq.respectTransparency false

/-- A continuous polynomial at the reciprocal-order limit is bounded. -/
theorem continuous_comp_carouselScale_isBigO_one (f : ℝ → ℝ) (hf : Continuous f) :
    (fun m => f (carouselScale m)) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  exact isBigO_const_of_tendsto (hf.tendsto 0 |>.comp carouselScale_tendsto) one_ne_zero

/-- Finite quotient algebra with a rigorously retained sixth-order error.
The coefficient equations are purely algebraic and are discharged in the
actual-carousel endpoint, not assumed Taylor data. -/
theorem quotient_expansion_sixth {N D E : ℕ → ℝ}
    (n₀ n₂ n₄ d₀ d₂ d₄ e₅ r₀ r₂ r₄ r₅ : ℝ)
    (hN : (fun m => N m-(n₀+n₂*carouselScale m^2+n₄*carouselScale m^4)) =O[atTop]
      (fun m => carouselScale m^6))
    (hD : (fun m => D m-(d₀+d₂*carouselScale m^2+d₄*carouselScale m^4)) =O[atTop]
      (fun m => carouselScale m^6))
    (hE : (fun m => E m-(1+e₅*carouselScale m^5)) =O[atTop] (fun m => carouselScale m^6))
    (hNt : Tendsto N atTop (𝓝 n₀)) (hDt : Tendsto D atTop (𝓝 d₀)) (hd₀ : d₀ ≠ 0)
    (he₀ : r₀*d₀=n₀) (he₂ : r₀*d₂+r₂*d₀=n₂)
    (he₄ : r₀*d₄+r₂*d₂+r₄*d₀=n₄) (he₅ : r₅*d₀=e₅*n₀) :
    (fun m => E m*N m/D m-(r₀+r₂*carouselScale m^2+r₄*carouselScale m^4+
      r₅*carouselScale m^5)) =O[atTop] (fun m => carouselScale m^6) := by
  let np (m : ℕ) := n₀+n₂*carouselScale m^2+n₄*carouselScale m^4
  let dp (m : ℕ) := d₀+d₂*carouselScale m^2+d₄*carouselScale m^4
  let ep (m : ℕ) := 1+e₅*carouselScale m^5
  let rp (m : ℕ) := r₀+r₂*carouselScale m^2+r₄*carouselScale m^4+r₅*carouselScale m^5
  have hNb : N =O[atTop] (fun _ : ℕ => (1 : ℝ)) := isBigO_const_of_tendsto hNt one_ne_zero
  have hEPb : ep =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    continuous_comp_carouselScale_isBigO_one (fun x => 1+e₅*x^5) (by fun_prop)
  have hRPb : rp =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    continuous_comp_carouselScale_isBigO_one (fun x => r₀+r₂*x^2+r₄*x^4+r₅*x^5) (by fun_prop)
  have hEN : (fun m => E m*N m-ep m*np m) =O[atTop] (fun m => carouselScale m^6) := by
    have h₁ : (fun m => (E m-ep m)*N m) =O[atTop] (fun m => carouselScale m^6) := by
      simpa only [mul_one] using hE.mul hNb
    have h₂ : (fun m => ep m*(N m-np m)) =O[atTop] (fun m => carouselScale m^6) := by
      simpa only [one_mul] using hEPb.mul hN
    convert h₁.add h₂ using 1
    funext m
    ring
  let Q (x : ℝ) := -(r₂*d₄+r₄*d₂)+(e₅*n₂-r₅*d₂)*x-r₄*d₄*x^2+(e₅*n₄-r₅*d₄)*x^3
  have hQ : (fun m => Q (carouselScale m)) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    continuous_comp_carouselScale_isBigO_one Q (by dsimp [Q]; fun_prop)
  have hpoly : (fun m => ep m*np m-rp m*dp m) =O[atTop] (fun m => carouselScale m^6) := by
    have h := (isBigO_refl (fun m => carouselScale m^6) atTop).mul hQ
    convert h using 1
    · funext m
      dsimp [ep, np, rp, dp, Q]
      linear_combination -he₀-carouselScale m^2*he₂-carouselScale m^4*he₄-carouselScale m^5*he₅
    · funext m
      ring
  have hRD : (fun m => rp m*(D m-dp m)) =O[atTop] (fun m => carouselScale m^6) := by
    simpa only [one_mul] using hRPb.mul hD
  have hnum : (fun m => E m*N m-rp m*D m) =O[atTop] (fun m => carouselScale m^6) := by
    convert (hEN.add hpoly).sub hRD using 1
    funext m
    ring
  have hDi : (fun m => (D m)⁻¹) =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    isBigO_const_of_tendsto (hDt.inv₀ hd₀) one_ne_zero
  have hh : (fun m => (E m*N m-rp m*D m)*(D m)⁻¹) =O[atTop]
      (fun m => carouselScale m^6) := by
    simpa only [mul_one] using hnum.mul hDi
  apply hh.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hDt.eventually_ne hd₀] with m hm
  change (E m*N m-rp m*D m)*(D m)⁻¹ = E m*N m/D m-rp m
  field_simp

end TournamentHamiltonian
