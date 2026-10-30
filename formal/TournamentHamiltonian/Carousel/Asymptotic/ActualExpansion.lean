module
public import TournamentHamiltonian.Carousel.Asymptotic.QuotientAlgebra

@[expose] public section
namespace TournamentHamiltonian
open Asymptotics Filter Topology
set_option backward.isDefEq.respectTransparency false

noncomputable def carouselA2 : ℝ := (Real.tanh 1-Real.tan 1)/3
noncomputable def carouselA4 : ℝ := (Real.tanh 1+Real.tan 1)/5+
  (1+(Real.tan 1)^2-Real.tanh 1*Real.tan 1)/9

/-- The simplified quartic coefficient equals exactly the paper's ell4+a2²/2. -/
theorem carouselA4_eq_manuscript : carouselA4 =
    (Real.tanh 1+Real.tan 1)/5+(2+(Real.tan 1)^2-(Real.tanh 1)^2)/18+
      carouselA2^2/2 := by
  unfold carouselA4 carouselA2
  ring

private theorem beta_sequence_tendsto :
    Tendsto (fun m => carouselBeta (carouselScale m)) atTop (𝓝 1) := by
  have hb : (fun m => carouselBeta (carouselScale m)-
      (1+(1/3 : ℝ)*carouselScale m^2+carouselScale m^4/5)) =O[atTop]
      (fun m => carouselScale m^6) := by
    convert carouselBeta_error_isBigO using 1
    funext m
    ring
  exact delta_tendsto_one (delta_second_bound (1/3) (delta_fourth_bound (1/3) hb))

private theorem alpha_sequence_tendsto :
    Tendsto (fun m => carouselAlpha (carouselScale m)) atTop (𝓝 1) := by
  have ha : (fun m => carouselAlpha (carouselScale m)-
      (1+(-1/3 : ℝ)*carouselScale m^2+carouselScale m^4/5)) =O[atTop]
      (fun m => carouselScale m^6) := by
    convert carouselAlpha_error_isBigO using 1
    funext m
    ring
  exact delta_tendsto_one (delta_second_bound (-1/3) (delta_fourth_bound (-1/3) ha))

/-- The manuscript's high-order expansion for the ACTUAL regular carousel
constant, with an unconditional sixth-order Big-O remainder. -/
theorem regularCarouselConstant_sixth_expansion :
    (fun m => regularCarouselConstant m - lowerConstant *
      (1+carouselA2*carouselScale m^2+carouselA4*carouselScale m^4-carouselScale m^5/3))
      =O[atTop] (fun m => carouselScale m^6) := by
  have hN := carouselCoshBeta_sixth_remainder
  have hD : (fun m => Real.cos (carouselAlpha (carouselScale m)) -
      (Real.cos 1+Real.sin 1/3*carouselScale m^2+
        (-Real.sin 1/5-Real.cos 1/18)*carouselScale m^4)) =O[atTop]
      (fun m => carouselScale m^6) := by
    convert carouselCosAlpha_sixth_remainder using 1
    funext m
    ring
  have hE : (fun m => Real.exp (carouselP (carouselScale m))-
      (1+(-1/3 : ℝ)*carouselScale m^5)) =O[atTop] (fun m => carouselScale m^6) := by
    convert carouselExpP_sixth_remainder using 1
    funext m
    ring
  have hNt := Real.continuous_cosh.tendsto 1 |>.comp beta_sequence_tendsto
  have hDt := Real.continuous_cos.tendsto 1 |>.comp alpha_sequence_tendsto
  have hc := cos_one_pos.ne'
  have hh := (Real.cosh_pos 1).ne'
  have he₀ : lowerConstant*Real.cos 1=Real.cosh 1 := by
    unfold lowerConstant
    field_simp
  have he₂ : lowerConstant*(Real.sin 1/3)+
      (lowerConstant*carouselA2)*Real.cos 1=Real.sinh 1/3 := by
    unfold lowerConstant carouselA2
    rw [Real.tanh_eq_sinh_div_cosh, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have he₄ : lowerConstant*(-Real.sin 1/5-Real.cos 1/18)+
      (lowerConstant*carouselA2)*(Real.sin 1/3)+
      (lowerConstant*carouselA4)*Real.cos 1=Real.sinh 1/5+Real.cosh 1/18 := by
    unfold lowerConstant carouselA2 carouselA4
    rw [Real.tanh_eq_sinh_div_cosh, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have he₅ : (-lowerConstant/3)*Real.cos 1=(-1/3 : ℝ)*Real.cosh 1 := by
    unfold lowerConstant
    field_simp
  have h := quotient_expansion_sixth
    (N := fun m => Real.cosh (carouselBeta (carouselScale m)))
    (D := fun m => Real.cos (carouselAlpha (carouselScale m)))
    (E := fun m => Real.exp (carouselP (carouselScale m)))
    (Real.cosh 1) (Real.sinh 1/3) (Real.sinh 1/5+Real.cosh 1/18)
    (Real.cos 1) (Real.sin 1/3) (-Real.sin 1/5-Real.cos 1/18) (-1/3)
    lowerConstant (lowerConstant*carouselA2) (lowerConstant*carouselA4) (-lowerConstant/3)
    hN hD hE hNt hDt hc he₀ he₂ he₄ he₅
  apply h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [regularCarouselConstant_real_form m hm]
  dsimp [carouselScale]
  ring

/-- The normalized form printed in Section 10.4. No first- or third-order term occurs. -/
theorem regularCarouselConstant_ratio_sixth_expansion :
    (fun m => regularCarouselConstant m/lowerConstant -
      (1+carouselA2*carouselScale m^2+carouselA4*carouselScale m^4-carouselScale m^5/3))
      =O[atTop] (fun m => carouselScale m^6) := by
  have hL : lowerConstant ≠ 0 := div_ne_zero (Real.cosh_pos 1).ne' cos_one_pos.ne'
  have h := regularCarouselConstant_sixth_expansion.const_mul_left (1/lowerConstant)
  convert h using 1
  funext m
  field_simp

/-- Explicit uniform quantifiers on the sixth-order remainder at odd orders. -/
theorem regularCarouselConstant_sixth_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, 1 ≤ M ∧ ∀ m : ℕ, M ≤ m →
      |regularCarouselConstant m/lowerConstant -
        (1+carouselA2/(2*(m : ℝ)+1)^2+carouselA4/(2*(m : ℝ)+1)^4-
          1/(3*(2*(m : ℝ)+1)^5))| ≤ C/(2*(m : ℝ)+1)^6 := by
  obtain ⟨C,hC,hO⟩ := regularCarouselConstant_ratio_sixth_expansion.exists_nonneg
  obtain ⟨M,hM⟩ := eventually_atTop.mp hO.bound
  refine ⟨C,hC,max M 1,le_max_right _ _,?_⟩
  intro m hm
  have hh := hM m ((le_max_left M 1).trans hm)
  simp only [Real.norm_eq_abs, abs_pow, abs_of_pos (carouselScale_pos m)] at hh
  convert hh using 1 <;> dsimp [carouselScale] <;> field_simp

end TournamentHamiltonian
