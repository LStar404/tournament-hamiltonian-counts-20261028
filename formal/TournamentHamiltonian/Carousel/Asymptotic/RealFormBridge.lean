module
public import TournamentHamiltonian.Carousel.Asymptotic.AlphaRemainder
public import TournamentHamiltonian.Carousel.Asymptotic.PRemainder
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section
namespace TournamentHamiltonian
set_option backward.isDefEq.respectTransparency false

/-- The right-half-plane logarithm used by the manuscript, proved on its actual points. -/
theorem complex_log_one_add_real_mul_I (x : ℝ) :
    Complex.log (1 + (x : ℂ)*Complex.I) =
      (Real.log (1+x^2)/2 : ℝ) + (Real.arctan x : ℂ)*Complex.I := by
  have hn : ‖(1 : ℂ)+(x : ℂ)*Complex.I‖ = Real.sqrt (1+x^2) := by
    rw [Complex.norm_def]
    congr 1
    simpa using Complex.normSq_add_mul_I 1 x
  apply Complex.ext
  · simp only [Complex.log_re, hn, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      zero_mul, sub_zero, add_zero]
    exact Real.log_sqrt (by positivity)
  · rw [Complex.log_im, Complex.arg_of_re_nonneg (by simp)]
    simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      mul_one, Complex.ofReal_re, Complex.I_re, mul_zero, add_zero, zero_add, hn]
    exact (Real.arctan_eq_arcsin x).symm

private theorem twice_exp_mul_cosh (a b : ℝ) :
    2*Real.exp a*Real.cosh b = Real.exp (a+b)+Real.exp (a-b) := by
  rw [Real.cosh_eq, sub_eq_add_neg, Real.exp_add, Real.exp_add]
  ring

/-- Real polynomial powers expressed without branch ambiguity. -/
theorem real_binomial_sum_exp_cosh (n : ℕ) (x : ℝ) (hx : |x| < 1) :
    (1+x)^n+(1-x)^n =
      2*Real.exp ((n : ℝ)/2*Real.log (1-x^2))*
        Real.cosh ((n : ℝ)/2*Real.log ((1+x)/(1-x))) := by
  have hplus : 0 < 1+x := by linarith [(abs_lt.mp hx).1]
  have hminus : 0 < 1-x := by linarith [(abs_lt.mp hx).2]
  have hl : Real.log (1-x^2) = Real.log (1+x)+Real.log (1-x) := by
    rw [show 1-x^2=(1+x)*(1-x) by ring, Real.log_mul hplus.ne' hminus.ne']
  rw [twice_exp_mul_cosh, hl, Real.log_div hplus.ne' hminus.ne']
  have hp : (n : ℝ)/2*(Real.log (1+x)+Real.log (1-x))+
      (n : ℝ)/2*(Real.log (1+x)-Real.log (1-x)) = n*Real.log (1+x) := by ring
  have hm : (n : ℝ)/2*(Real.log (1+x)+Real.log (1-x))-
      (n : ℝ)/2*(Real.log (1+x)-Real.log (1-x)) = n*Real.log (1-x) := by ring
  rw [hp, hm, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hplus, Real.exp_log hminus]

private theorem twice_exp_mul_cos (a b : ℂ) :
    2*Complex.exp a*Complex.cos b =
      Complex.exp (a+b*Complex.I)+Complex.exp (a-b*Complex.I) := by
  rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_add,
    show -(b*Complex.I)=(-b)*Complex.I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  ring

/-- The imaginary polynomial powers expressed through the real cosine. -/
theorem complex_binomial_sum_exp_cos (n : ℕ) (x : ℝ) :
    (1+(x : ℂ)*Complex.I)^n+(1-(x : ℂ)*Complex.I)^n =
      (2*Real.exp ((n : ℝ)/2*Real.log (1+x^2))*Real.cos ((n : ℝ)*Real.arctan x) : ℝ) := by
  have hp : (1+(x : ℂ)*Complex.I)^n =
      Complex.exp ((n : ℂ)*Complex.log (1+(x : ℂ)*Complex.I)) := by
    rw [Complex.exp_nat_mul, Complex.exp_log (by intro h; have := congrArg Complex.re h; simp at this)]
  have hm : (1-(x : ℂ)*Complex.I)^n =
      Complex.exp ((n : ℂ)*Complex.log (1-(x : ℂ)*Complex.I)) := by
    rw [Complex.exp_nat_mul, Complex.exp_log (by intro h; have := congrArg Complex.re h; simp at this)]
  rw [hp, hm, show (1 : ℂ)-(x : ℂ)*Complex.I=1+((-x : ℝ) : ℂ)*Complex.I by push_cast; ring,
    complex_log_one_add_real_mul_I, complex_log_one_add_real_mul_I]
  simp only [neg_sq, Real.arctan_neg, Complex.ofReal_neg]
  push_cast
  rw [twice_exp_mul_cos]
  congr 1 <;> congr 1 <;> ring

theorem carouselAlpha_cos_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.cos (carouselAlpha x) := by
  have ha0 : 0 < carouselAlpha x := div_pos (Real.arctan_pos.mpr hx) hx
  have ha1 : carouselAlpha x ≤ 1 := by
    exact (div_le_one hx).mpr (Real.arctan_le_self hx.le)
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_gt_three]

/-- The original polynomial determinant ratio at every integer order greater
than one is exactly the manuscript's real elementary expression. -/
theorem transitiveRatio_real_form (n : ℕ) (hn : 1 < n) :
    transitiveRatio n =
      (Real.exp (carouselP (1/(n : ℝ))-1/(n : ℝ))*
        Real.cosh (carouselBeta (1/(n : ℝ))) /
        Real.cos (carouselAlpha (1/(n : ℝ))) : ℝ) := by
  let x : ℝ := 1/n
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : |x| < 1 := by
    rw [abs_of_pos hx0]
    dsimp [x]
    exact (div_lt_one (by linarith : (0 : ℝ) < n)).mpr hnR
  have ha : (n : ℝ)*Real.arctan x = carouselAlpha x := by
    unfold carouselAlpha
    dsimp [x]
    field_simp
  have hb : (n : ℝ)/2*Real.log ((1+x)/(1-x)) = carouselBeta x := by
    unfold carouselBeta
    dsimp [x]
    field_simp
  have hnum := real_binomial_sum_exp_cosh n x hx1
  rw [hb] at hnum
  have hden := complex_binomial_sum_exp_cos n x
  rw [ha] at hden
  have hnumC : ((1+(1 : ℂ)/n)^n+(1-1/n)^n) =
      (((1+x)^n+(1-x)^n : ℝ) : ℂ) := by
    dsimp [x]
    push_cast
    rfl
  have hxI : (x : ℂ)*Complex.I = Complex.I/n := by
    dsimp [x]
    push_cast
    ring
  rw [hxI] at hden
  rw [transitiveRatio_eq_binomialMean]
  simp only [binomialMean]
  rw [hnumC, hnum, hden, div_div_div_cancel_right₀ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [← Complex.ofReal_div]
  apply congrArg Complex.ofReal
  change _ = Real.exp (carouselP x-x)*Real.cosh (carouselBeta x)/Real.cos (carouselAlpha x)
  have hp : carouselP x-x = (n : ℝ)/2*Real.log (1-x^2) -
      (n : ℝ)/2*Real.log (1+x^2) := by
    unfold carouselP
    dsimp [x]
    field_simp
    ring
  rw [hp, Real.exp_sub]
  have hc := carouselAlpha_cos_pos hx0
  field_simp

/-- The real function used for expansion is exactly the ACTUAL regular carousel
constant at each reciprocal odd order. This is the integer-power bridge. -/
theorem regularCarouselConstant_real_form (m : ℕ) (hm : 1 ≤ m) :
    regularCarouselConstant m =
      Real.exp (carouselP (1/(2*(m : ℝ)+1))) *
        Real.cosh (carouselBeta (1/(2*(m : ℝ)+1))) /
        Real.cos (carouselAlpha (1/(2*(m : ℝ)+1))) := by
  have hr := carousel_spectralRatio_eq m
  rw [transitiveRatio_real_form (2*m+1) (by omega)] at hr
  have hrR := Complex.ofReal_injective hr
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hrR
  rw [regularCarouselConstant, hrR, ← mul_div_assoc, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end TournamentHamiltonian
