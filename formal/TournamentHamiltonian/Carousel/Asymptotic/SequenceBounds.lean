module
public import TournamentHamiltonian.Carousel.Asymptotic.CompositeTaylor

@[expose] public section
namespace TournamentHamiltonian
open Asymptotics Filter Topology
set_option backward.isDefEq.respectTransparency false

noncomputable def carouselScale (m : ℕ) : ℝ := 1/(2*(m : ℝ)+1)

theorem carouselScale_pos (m : ℕ) : 0 < carouselScale m := by unfold carouselScale; positivity

theorem carouselScale_le_one (m : ℕ) : carouselScale m ≤ 1 := by
  unfold carouselScale
  apply (div_le_one (by positivity : (0 : ℝ) < 2*m+1)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) m]

theorem carouselScale_le_third (m : ℕ) (hm : 1 ≤ m) : carouselScale m ≤ 1/3 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  unfold carouselScale
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2*m+1) (by norm_num : (0 : ℝ) < 3)).mpr
  linarith

theorem carouselScale_tendsto : Tendsto carouselScale atTop (𝓝 0) := by
  have ho : Tendsto (fun m : ℕ => 2*m+1) atTop atTop := by
    apply tendsto_atTop_mono (f := fun m : ℕ => m) (fun m => by omega) tendsto_id
  have h := tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ) |>.comp ho)
  change Tendsto (fun m : ℕ => 1/(2*(m : ℝ)+1)) atTop (𝓝 0)
  simpa [Function.comp_def, one_div] using h

theorem carouselScale_pow_isBigO {a b : ℕ} (hba : b ≤ a) :
    (fun m => carouselScale m^a) =O[atTop] (fun m => carouselScale m^b) := by
  apply IsBigO.of_bound 1
  filter_upwards with m
  simp only [Real.norm_eq_abs, abs_pow, abs_of_pos (carouselScale_pos m), one_mul]
  exact pow_le_pow_of_le_one (carouselScale_pos m).le (carouselScale_le_one m) hba

theorem carouselBeta_error_isBigO :
    (fun m => carouselBeta (carouselScale m) -
      (1+carouselScale m^2/3+carouselScale m^4/5)) =O[atTop] (fun m => carouselScale m^6) := by
  apply IsBigO.of_bound (9/8)
  filter_upwards [eventually_ge_atTop 1] with m hm
  simpa only [Real.norm_eq_abs, abs_pow, abs_of_pos (carouselScale_pos m)] using
    carouselBeta_sixth_remainder_third (carouselScale_pos m) (carouselScale_le_third m hm)

theorem carouselAlpha_error_isBigO :
    (fun m => carouselAlpha (carouselScale m) -
      (1-carouselScale m^2/3+carouselScale m^4/5)) =O[atTop] (fun m => carouselScale m^6) := by
  apply IsBigO.of_bound 1
  filter_upwards with m
  simpa only [Real.norm_eq_abs, abs_pow, abs_of_pos (carouselScale_pos m), one_mul] using
    carouselAlpha_sixth_remainder (carouselScale_pos m)

theorem carouselP_error_isBigO :
    (fun m => carouselP (carouselScale m) + carouselScale m^5/3) =O[atTop]
      (fun m => carouselScale m^9) := by
  apply IsBigO.of_bound (81/80)
  filter_upwards [eventually_ge_atTop 1] with m hm
  simpa only [Real.norm_eq_abs, abs_pow, abs_of_pos (carouselScale_pos m)] using
    carouselP_ninth_remainder_third (carouselScale_pos m) (carouselScale_le_third m hm)

/-- Algebra of the proved sixth-order remainders. This auxiliary implication is
instantiated below with the actual alpha and beta estimates. -/
theorem delta_fourth_bound {f : ℕ → ℝ} (a : ℝ)
    (hf : (fun m => f m-(1+a*carouselScale m^2+carouselScale m^4/5)) =O[atTop]
      (fun m => carouselScale m^6)) :
    (fun m => f m-1-a*carouselScale m^2) =O[atTop] (fun m => carouselScale m^4) := by
  have h := (hf.trans (carouselScale_pow_isBigO (by omega : 4 ≤ 6))).add
    ((isBigO_refl (fun m => carouselScale m^4) atTop).const_mul_left (1/5))
  convert h using 1
  funext m
  ring

theorem delta_second_bound {f : ℕ → ℝ} (a : ℝ)
    (hf : (fun m => f m-1-a*carouselScale m^2) =O[atTop] (fun m => carouselScale m^4)) :
    (fun m => f m-1) =O[atTop] (fun m => carouselScale m^2) := by
  have h := (hf.trans (carouselScale_pow_isBigO (by omega : 2 ≤ 4))).add
    ((isBigO_refl (fun m => carouselScale m^2) atTop).const_mul_left a)
  convert h using 1
  funext m
  ring

theorem delta_square_sixth_bound {f : ℕ → ℝ} (a : ℝ)
    (hf : (fun m => f m-1-a*carouselScale m^2) =O[atTop] (fun m => carouselScale m^4)) :
    (fun m => (f m-1)^2-a^2*carouselScale m^4) =O[atTop] (fun m => carouselScale m^6) := by
  have hplus := (delta_second_bound a hf).add
    ((isBigO_refl (fun m => carouselScale m^2) atTop).const_mul_left a)
  have h := hf.mul hplus
  convert h using 1 <;> funext m <;> ring

theorem delta_tendsto_one {f : ℕ → ℝ}
    (hf : (fun m => f m-1) =O[atTop] (fun m => carouselScale m^2)) :
    Tendsto f atTop (𝓝 1) := by
  apply tendsto_sub_nhds_zero_iff.mp
  exact hf.trans_tendsto (by simpa using carouselScale_tendsto.pow 2)

end TournamentHamiltonian
