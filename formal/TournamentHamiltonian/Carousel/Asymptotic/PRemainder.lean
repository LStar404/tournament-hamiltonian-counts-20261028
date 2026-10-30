module
public import TournamentHamiltonian.Carousel.Asymptotic.BetaRemainder

@[expose] public section
namespace TournamentHamiltonian
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's original common logarithmic correction. -/
noncomputable def carouselP (x : ℝ) : ℝ :=
  x + (Real.log (1-x^2)-Real.log (1+x^2))/(2*x)

/-- A genuine ninth-order remainder for the logarithmic correction.
The coefficient `1/(1-|x|^4)` is a sufficient coarse bound, not the paper's
sharper coefficient `1/(5*(1-|x|^4))`. -/
theorem carouselP_ninth_remainder {x : ℝ} (hx0 : x ≠ 0) (hx : |x| < 1) :
    |carouselP x + x^5/3| ≤ |x|^9/(1-x^4) := by
  have hx2 : x^2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
  have hminus : 0 < 1-x^2 := by linarith
  have hplus : 0 < 1+x^2 := by positivity
  have hs := Real.sum_range_sub_log_div_le
    (show |x^2| < 1 by rwa [abs_of_nonneg (sq_nonneg x)]) 2
  norm_num [Finset.sum_range_succ, ← pow_mul, abs_pow] at hs
  have hlog : (1/2 : ℝ)*Real.log ((1+x^2)/(1-x^2)) =
      (Real.log (1+x^2)-Real.log (1-x^2))/2 := by
    rw [Real.log_div hplus.ne' hminus.ne']
    ring
  have heq : carouselP x + x^5/3 =
      -(1/2*Real.log ((1+x^2)/(1-x^2)) - (x^2+x^6/3))/x := by
    rw [hlog]
    unfold carouselP
    field_simp
    ring
  rw [heq, abs_div, abs_neg]
  calc
    |1/2*Real.log ((1+x^2)/(1-x^2)) - (x^2+x^6/3)|/|x| ≤
        (|x|^10/(1-x^4))/|x| := by
          have habs10 : |x|^10 = x^10 := by
            rw [show 10=2*5 by norm_num, pow_mul, sq_abs, ← pow_mul]
          rw [habs10]
          exact div_le_div_of_nonneg_right hs (abs_nonneg x)
    _ = |x|^9/(1-x^4) := by
      have hx4 : x^4 < 1 := by nlinarith [sq_nonneg (x^2), sq_nonneg x]
      field_simp [abs_ne_zero.mpr hx0, show 1-x^4 ≠ 0 by linarith]

/-- A uniform O(x^9) constant throughout the manuscript's interval. -/
theorem carouselP_ninth_remainder_third {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1/3) :
    |carouselP x + x^5/3| ≤ (81/80)*x^9 := by
  have hxabs : |x| < 1 := by rw [abs_of_pos hx0]; linarith
  have hh := carouselP_ninth_remainder hx0.ne' hxabs
  rw [abs_of_pos hx0] at hh
  apply hh.trans
  have hx4 : x^4 ≤ (1/3 : ℝ)^4 := pow_le_pow_left₀ hx0.le hx 4
  have hden : 0 < 1-x^4 := by norm_num at hx4; linarith
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_nonneg (show 0 ≤ 1/81-x^4 by norm_num at hx4; linarith)
    (pow_nonneg hx0.le 9)]

end TournamentHamiltonian
