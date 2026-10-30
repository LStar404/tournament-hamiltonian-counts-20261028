module
public import TournamentHamiltonian.Carousel.Asymptotic.BetaRemainder
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section
namespace TournamentHamiltonian
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's original arctangent quotient. -/
noncomputable def carouselAlpha (x : ℝ) : ℝ := Real.arctan x / x

/-- The remainder derivative is computed exactly, rather than assumed as a Taylor datum. -/
theorem hasDerivAt_arctan_fifth_remainder (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arctan y - (y-y^3/3+y^5/5))
      (-x^6/(1+x^2)) x := by
  have h := (Real.hasDerivAt_arctan x).sub
    (((hasDerivAt_id x).sub ((hasDerivAt_pow 3 x).div_const 3)).add
      ((hasDerivAt_pow 5 x).div_const 5))
  convert h using 1
  · funext y
    simp only [Pi.sub_apply, Pi.add_apply, id_eq]
  · norm_num
    field_simp
    ring

/-- A direct mean-value bound for the arctangent truncation on a nonnegative segment. -/
theorem arctan_fifth_remainder_bound {x : ℝ} (hx : 0 ≤ x) :
    |Real.arctan x - (x-x^3/3+x^5/5)| ≤ x^7 := by
  let f (y : ℝ) := Real.arctan y - (y-y^3/3+y^5/5)
  let f' (y : ℝ) := -y^6/(1+y^2)
  have hd (y : ℝ) (_hy : y ∈ Set.Icc 0 x) : HasDerivWithinAt f (f' y) (Set.Icc 0 x) y :=
    (hasDerivAt_arctan_fifth_remainder y).hasDerivWithinAt
  have hb (y : ℝ) (hy : y ∈ Set.Icc 0 x) : ‖f' y‖ ≤ x^6 := by
    simp only [f', Real.norm_eq_abs, abs_div, abs_neg, abs_pow,
      abs_of_nonneg hy.1, abs_of_nonneg (by positivity : 0 ≤ 1+y^2)]
    exact (div_le_self (b := 1+y^2) (pow_nonneg hy.1 6) (by nlinarith [sq_nonneg y])).trans
      (pow_le_pow_left₀ hy.1 hy.2 6)
  have hh := (convex_Icc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (show (0 : ℝ) ∈ Set.Icc 0 x from ⟨le_rfl, hx⟩)
    (show x ∈ Set.Icc 0 x from ⟨hx, le_rfl⟩)
  simpa only [f, Real.arctan_zero, zero_pow (by omega : 3 ≠ 0),
    zero_pow (by omega : 5 ≠ 0), zero_div, sub_zero, zero_add,
    Real.norm_eq_abs, abs_of_nonneg hx, ← pow_succ] using hh

/-- A sixth-order explicit remainder for the original alpha function.
The coefficient 1 is sufficient, although not the paper's sharper coefficient. -/
theorem carouselAlpha_sixth_remainder {x : ℝ} (hx : 0 < x) :
    |carouselAlpha x - (1-x^2/3+x^4/5)| ≤ x^6 := by
  have hh := arctan_fifth_remainder_bound hx.le
  have heq : carouselAlpha x - (1-x^2/3+x^4/5) =
      (Real.arctan x-(x-x^3/3+x^5/5))/x := by
    unfold carouselAlpha
    field_simp
  rw [heq, abs_div, abs_of_pos hx]
  apply (div_le_iff₀ hx).mpr
  simpa only [pow_succ] using hh

end TournamentHamiltonian
