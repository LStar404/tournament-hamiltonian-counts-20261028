module
public import TournamentHamiltonian.Carousel.CarouselConstants
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section
namespace TournamentHamiltonian
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's actual elementary beta function, with totalized division at zero. -/
noncomputable def carouselBeta (x : ℝ) : ℝ :=
  (1/2 * Real.log ((1+x)/(1-x))) / x

/-- A sixth-order explicit remainder bound for the original logarithmic beta,
not a Taylor expansion supplied as a premise. The constant is deliberately
coarser than the optimal `1/7`; it suffices for the required `O(x^6)`. -/
theorem carouselBeta_sixth_remainder {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 1) :
    |carouselBeta x - (1 + x^2/3 + x^4/5)| ≤ |x|^6 / (1-x^2) := by
  have hs := Real.sum_range_sub_log_div_le hx 3
  norm_num [Finset.sum_range_succ] at hs
  have heq : carouselBeta x - (1+x^2/3+x^4/5) =
      (1/2 * Real.log ((1+x)/(1-x)) - (x+x^3/3+x^5/5))/x := by
    unfold carouselBeta
    field_simp
  rw [heq, abs_div]
  calc
    |1/2 * Real.log ((1+x)/(1-x)) - (x+x^3/3+x^5/5)| / |x| ≤
        (|x|^7/(1-x^2))/|x| := div_le_div_of_nonneg_right hs (abs_nonneg x)
    _ = |x|^6/(1-x^2) := by
      have hd : 1-x^2 ≠ 0 := by
        have hlt : x^2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
        linarith
      field_simp [abs_ne_zero.mpr hx0, hd]

/-- A completely uniform bound on the manuscript's working interval. -/
theorem carouselBeta_sixth_remainder_third {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1/3) :
    |carouselBeta x - (1+x^2/3+x^4/5)| ≤ (9/8)*x^6 := by
  have hxabs : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have hh := carouselBeta_sixth_remainder hx0.ne' hxabs
  rw [abs_of_pos hx0] at hh
  apply hh.trans
  have hden : 0 < 1-x^2 := by nlinarith
  apply (div_le_iff₀ hden).mpr
  have hx2 : x^2 ≤ (1/3 : ℝ)^2 := pow_le_pow_left₀ hx0.le hx 2
  nlinarith [mul_nonneg (show 0 ≤ 1/9-x^2 by nlinarith) (pow_nonneg hx0.le 6)]

/-- The same explicit remainder at the actual carousel reciprocal odd orders.
This is an input to, not a claim of, the full regular-constant expansion. -/
theorem carouselBeta_sixth_remainder_odd_order (m : ℕ) (hm : 1 ≤ m) :
    |carouselBeta (1/(2*(m : ℝ)+1)) -
      (1 + 1/(3*(2*(m : ℝ)+1)^2) + 1/(5*(2*(m : ℝ)+1)^4))| ≤
      9/(8*(2*(m : ℝ)+1)^6) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : 0 < 2*(m : ℝ)+1 := by positivity
  have hx : 1/(2*(m : ℝ)+1) ≤ (1/3 : ℝ) := by
    apply (div_le_div_iff₀ hd (by norm_num : (0 : ℝ) < 3)).mpr
    linarith
  have hh := carouselBeta_sixth_remainder_third (one_div_pos.mpr hd) hx
  have hA : (1 + (1/(2*(m : ℝ)+1))^2/3 + (1/(2*(m : ℝ)+1))^4/5) =
      (1 + 1/(3*(2*(m : ℝ)+1)^2) + 1/(5*(2*(m : ℝ)+1)^4)) := by
    field_simp
  have hB : (9/8 : ℝ)*(1/(2*(m : ℝ)+1))^6 = 9/(8*(2*(m : ℝ)+1)^6) := by
    field_simp
  rw [hA, hB] at hh
  exact hh

end TournamentHamiltonian
