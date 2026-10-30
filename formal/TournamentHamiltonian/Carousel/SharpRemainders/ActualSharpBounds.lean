module
public import TournamentHamiltonian.Carousel.SharpRemainders.SharpRemainders

@[expose] public section
namespace TournamentHamiltonian
set_option backward.isDefEq.respectTransparency false

/-- Two-sided-domain version, obtained by actual artanh oddness. -/
theorem artanh_fifth_sharp {x : ℝ} (hx : |x| < 1) :
    |Real.artanh x-(x+x^3/3+x^5/5)| ≤ |x|^7/(7*(1-x^2)) := by
  by_cases hx0 : 0 ≤ x
  · simpa [abs_of_nonneg hx0] using
      artanh_fifth_sharp_nonneg hx0 ((le_abs_self x).trans_lt hx)
  · have hxn : 0 ≤ -x := by linarith
    have hh := artanh_fifth_sharp_nonneg hxn (by rw [abs_of_neg (by linarith)] at hx; exact hx)
    have heq : Real.artanh (-x)-((-x)+(-x)^3/3+(-x)^5/5) =
        -(Real.artanh x-(x+x^3/3+x^5/5)) := by
      rw [artanh_neg_open hx]
      ring
    rw [heq, abs_neg] at hh
    simpa only [even_two, Even.neg_pow, abs_of_neg (by linarith : x < 0)] using hh

/-- The alternating atan remainder has the stronger bound without a denominator. -/
theorem arctan_fifth_sharp (x : ℝ) :
    |Real.arctan x-(x-x^3/3+x^5/5)| ≤ |x|^7/7 := by
  by_cases hx0 : 0 ≤ x
  · simpa [abs_of_nonneg hx0] using arctan_fifth_sharp_nonneg hx0
  · have hh := arctan_fifth_sharp_nonneg (show 0 ≤ -x by linarith)
    have heq : Real.arctan (-x)-((-x)-(-x)^3/3+(-x)^5/5) =
        -(Real.arctan x-(x-x^3/3+x^5/5)) := by
      rw [Real.arctan_neg]
      ring
    rw [heq, abs_neg] at hh
    simpa only [abs_of_neg (by linarith : x < 0)] using hh

/-- Bridge from the existing logarithmic beta, not a newly substituted definition. -/
theorem carouselBeta_eq_artanh_div {x : ℝ} (hx : |x| < 1) :
    carouselBeta x = Real.artanh x / x := by
  have hh := abs_lt.mp hx
  rw [carouselBeta, Real.artanh_eq_half_log ⟨hh.1.le, hh.2.le⟩]

/-- Bridge from the existing p correction to its actual artanh expression. -/
theorem carouselP_eq_sub_artanh_sq {x : ℝ} (hx : |x| < 1) :
    carouselP x = x-Real.artanh (x^2)/x := by
  have hx2 : |x^2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg x)]
    exact (sq_lt_one_iff_abs_lt_one x).mpr hx
  rw [artanh_eq_log_difference hx2, carouselP]
  ring

/-- Stronger explicit alpha estimate, on the punctured real line. -/
theorem carouselAlpha_sixth_sharp_stronger {x : ℝ} (hx0 : 0 < |x|) :
    |carouselAlpha x-(1-x^2/3+x^4/5)| ≤ |x|^6/7 := by
  have hxne := abs_pos.mp hx0
  have heq : carouselAlpha x-(1-x^2/3+x^4/5) =
      (Real.arctan x-(x-x^3/3+x^5/5))/x := by
    unfold carouselAlpha
    field_simp
  rw [heq, abs_div]
  calc
    _ ≤ (|x|^7/7)/|x| := div_le_div_of_nonneg_right (arctan_fifth_sharp x) (abs_nonneg x)
    _ = |x|^6/7 := by field_simp [ne_of_gt hx0]

/-- Exactly the displayed manuscript alpha bound for 0<|x|<1. -/
theorem carouselAlpha_sixth_sharp {x : ℝ} (hx0 : 0 < |x|) (hx : |x| < 1) :
    |carouselAlpha x-(1-x^2/3+x^4/5)| ≤ |x|^6/(7*(1-x^2)) := by
  apply (carouselAlpha_sixth_sharp_stronger hx0).trans
  have hx2 := (sq_lt_one_iff_abs_lt_one x).mpr hx
  apply div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg x) _) (by nlinarith : 0 < 7*(1-x^2))
  nlinarith [sq_nonneg x]

/-- Exactly the displayed manuscript beta bound for 0<|x|<1. -/
theorem carouselBeta_sixth_sharp {x : ℝ} (hx0 : 0 < |x|) (hx : |x| < 1) :
    |carouselBeta x-(1+x^2/3+x^4/5)| ≤ |x|^6/(7*(1-x^2)) := by
  have hxne := abs_pos.mp hx0
  have heq : carouselBeta x-(1+x^2/3+x^4/5) =
      (Real.artanh x-(x+x^3/3+x^5/5))/x := by
    rw [carouselBeta_eq_artanh_div hx]
    field_simp
  rw [heq, abs_div]
  calc
    _ ≤ (|x|^7/(7*(1-x^2)))/|x| :=
      div_le_div_of_nonneg_right (artanh_fifth_sharp hx) (abs_nonneg x)
    _ = |x|^6/(7*(1-x^2)) := by
      have hd : 1-x^2 ≠ 0 := by
        have := (sq_lt_one_iff_abs_lt_one x).mpr hx
        linarith
      field_simp [ne_of_gt hx0, hd]

/-- Exactly the displayed manuscript p bound (including its absolute-value denominator). -/
theorem carouselP_ninth_sharp {x : ℝ} (hx0 : 0 < |x|) (hx : |x| < 1) :
    |carouselP x+x^5/3| ≤ |x|^9/(5*(1-|x|^4)) := by
  have hxne := abs_pos.mp hx0
  have hx2 : x^2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
  have hh := artanh_third_sharp_nonneg (sq_nonneg x) hx2
  have heq : carouselP x+x^5/3 = -(Real.artanh (x^2)-(x^2+(x^2)^3/3))/x := by
    rw [carouselP_eq_sub_artanh_sq hx]
    field_simp
    ring
  rw [heq, abs_div, abs_neg]
  calc
    _ ≤ ((x^2)^5/(5*(1-(x^2)^2)))/|x| :=
      div_le_div_of_nonneg_right hh (abs_nonneg x)
    _ = |x|^9/(5*(1-|x|^4)) := by
      have habs2 : |x|^2 = x^2 := sq_abs x
      have habs4 : |x|^4 = (x^2)^2 := by rw [show 4=2*2 by norm_num, pow_mul, habs2]
      have habs10 : |x|^10 = (x^2)^5 := by rw [show 10=2*5 by norm_num, pow_mul, habs2]
      rw [← habs4, ← habs10]
      have hd : 1-|x|^4 ≠ 0 := by
        have hx4 : |x|^4 < 1 := pow_lt_one₀ (abs_nonneg x) hx (by omega : 4 ≠ 0)
        linarith
      field_simp [ne_of_gt hx0, hd]

/-- The original quotient definitions are totalized at zero, NOT set to their limits. -/
theorem carousel_actual_zero_values :
    carouselAlpha 0 = 0 ∧ carouselBeta 0 = 0 ∧ carouselP 0 = 0 := by
  norm_num [carouselAlpha, carouselBeta, carouselP]

/-- Consequently neither alpha nor beta's punctured-domain remainder inequality
can simply be asserted at zero. -/
theorem carousel_alpha_beta_zero_remainders :
    |carouselAlpha 0-(1-(0 : ℝ)^2/3+(0 : ℝ)^4/5)| = 1 ∧
    |carouselBeta 0-(1+(0 : ℝ)^2/3+(0 : ℝ)^4/5)| = 1 := by
  norm_num [carouselAlpha, carouselBeta]

end TournamentHamiltonian
