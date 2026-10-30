module
public import TournamentHamiltonian.Carousel.Asymptotic.AlphaRemainder
public import TournamentHamiltonian.Carousel.Asymptotic.PRemainder
public import Mathlib.Analysis.SpecialFunctions.Artanh

@[expose] public section
namespace TournamentHamiltonian
open scoped Topology
set_option backward.isDefEq.respectTransparency false

private theorem compare_zero {f d : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hd : ∀ y ∈ Set.Icc 0 x, HasDerivAt f (d y) y)
    (hp : ∀ y ∈ Set.Icc 0 x, 0 ≤ d y) : f 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Icc 0 x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hd y (interior_subset hy)).deriv]
      exact hp y (interior_subset hy)
  exact hm ⟨le_rfl, hx⟩ ⟨hx, le_rfl⟩ hx

/-- Derivative comparison with an explicit polynomial primitive, used only for
these elementary remainder estimates. In particular, no Taylor hypothesis is used. -/
private theorem power_remainder_bound {f d : ℝ → ℝ} {x D : ℝ} (n : ℕ)
    (hx : 0 ≤ x) (hD : 0 < D)
    (hd : ∀ y ∈ Set.Icc 0 x, HasDerivAt f (d y) y)
    (hb : ∀ y ∈ Set.Icc 0 x, |d y| ≤ y^n / D) :
    |f x - f 0| ≤ x^(n+1)/((n+1 : ℝ)*D) := by
  let g (y : ℝ) := y^(n+1)/((n+1 : ℝ)*D)
  have hg (y : ℝ) : HasDerivAt g (y^n/D) y := by
    convert (hasDerivAt_pow (n+1) y).div_const ((n+1 : ℝ)*D) using 1
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    field_simp
  have h₁ := compare_zero hx
    (fun y hy => (hg y).sub (hd y hy))
    (fun y hy => sub_nonneg.mpr ((le_abs_self (d y)).trans (hb y hy)))
  have h₂ := compare_zero hx
    (fun y hy => (hg y).add (hd y hy))
    (fun y hy => by have hh := (abs_le.mp (hb y hy)).1; linarith)
  have hg0 : g 0 = 0 := by simp [g]
  change g 0 - f 0 ≤ g x - f x at h₁
  change g 0 + f 0 ≤ g x + f x at h₂
  rw [hg0] at h₁ h₂
  exact abs_le.mpr ⟨by dsimp [g] at h₂ ⊢; linarith,
    by dsimp [g] at h₁ ⊢; linarith⟩

/-- The actual inverse hyperbolic tangent equals its log difference in its open domain. -/
theorem artanh_eq_log_difference {x : ℝ} (hx : |x| < 1) :
    Real.artanh x = (Real.log (1+x)-Real.log (1-x))/2 := by
  have hh := abs_lt.mp hx
  rw [Real.artanh_eq_half_log ⟨hh.1.le, hh.2.le⟩,
    Real.log_div (by linarith : 1+x ≠ 0) (by linarith : 1-x ≠ 0)]
  ring

/-- Derivative obtained directly from the logarithms on (-1,1). -/
theorem hasDerivAt_artanh_open {x : ℝ} (hx : |x| < 1) :
    HasDerivAt Real.artanh (1/(1-x^2)) x := by
  have hh := abs_lt.mp hx
  have h := (((hasDerivAt_id x).const_add 1).log
    (by linarith : 1+x ≠ 0)).sub
    (((hasDerivAt_id x).const_sub 1).log (by linarith : 1-x ≠ 0))
  have hd : HasDerivAt (fun y : ℝ => (Real.log (1+y)-Real.log (1-y))/2)
      (1/(1-x^2)) x := by
    convert h.div_const 2 using 1
    simp only [id_eq]
    norm_num
    have hs : 1-x^2 ≠ 0 := by
      have := (sq_lt_one_iff_abs_lt_one x).mpr hx
      linarith
    field_simp [hs, show 1+x ≠ 0 by linarith, show 1-x ≠ 0 by linarith]
    simp only [id_eq]
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hh] with y hy
  exact artanh_eq_log_difference (abs_lt.mpr hy)

/-- Oddness, with the domain explicit (the library's totalized artanh is not
being assigned a branch identity outside this interval). -/
theorem artanh_neg_open {x : ℝ} (hx : |x| < 1) :
    Real.artanh (-x) = -Real.artanh x := by
  rw [artanh_eq_log_difference (by simpa using hx), artanh_eq_log_difference hx]
  simp only [sub_eq_add_neg, neg_neg]
  ring

private theorem hasDerivAt_artanh_fifth {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun y : ℝ => Real.artanh y-(y+y^3/3+y^5/5))
      (x^6/(1-x^2)) x := by
  have h := (hasDerivAt_artanh_open hx).sub
    (((hasDerivAt_id x).add ((hasDerivAt_pow 3 x).div_const 3)).add
      ((hasDerivAt_pow 5 x).div_const 5))
  convert h using 1
  · funext y; simp
  · have hs : 1-x^2 ≠ 0 := by
      have := (sq_lt_one_iff_abs_lt_one x).mpr hx
      linarith
    norm_num
    field_simp [hs]
    ring

private theorem hasDerivAt_artanh_third {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun y : ℝ => Real.artanh y-(y+y^3/3))
      (x^4/(1-x^2)) x := by
  have h := (hasDerivAt_artanh_open hx).sub
    ((hasDerivAt_id x).add ((hasDerivAt_pow 3 x).div_const 3))
  convert h using 1
  · funext y; simp
  · have hs : 1-x^2 ≠ 0 := by
      have := (sq_lt_one_iff_abs_lt_one x).mpr hx
      linarith
    norm_num
    field_simp [hs]
    ring

private theorem segment_rational_bound {x y : ℝ} (hx : x < 1)
    (hy : y ∈ Set.Icc 0 x) (n : ℕ) :
    |y^n/(1-y^2)| ≤ y^n/(1-x^2) := by
  have hx0 := hy.1.trans hy.2
  have hx2 : x^2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr (by rwa [abs_of_nonneg hx0])
  have hy2 : y^2 ≤ x^2 := pow_le_pow_left₀ hy.1 hy.2 2
  have hyden : 0 < 1-y^2 := by linarith
  rw [abs_of_nonneg (div_nonneg (pow_nonneg hy.1 _) hyden.le)]
  exact div_le_div_of_nonneg_left (pow_nonneg hy.1 _) (by linarith) (by linarith)

/-- Sharp geometric-denominator bound for the actual artanh fifth truncation. -/
theorem artanh_fifth_sharp_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    |Real.artanh x-(x+x^3/3+x^5/5)| ≤ x^7/(7*(1-x^2)) := by
  have hx2 : x^2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr (by rwa [abs_of_nonneg hx0])
  have hh := power_remainder_bound 6 hx0 (show 0 < 1-x^2 by linarith)
    (fun y hy => hasDerivAt_artanh_fifth (by rw [abs_of_nonneg hy.1]; exact hy.2.trans_lt hx))
    (fun y hy => segment_rational_bound hx hy 6)
  norm_num at hh ⊢
  exact hh

/-- Sharp geometric-denominator bound for the actual artanh third truncation. -/
theorem artanh_third_sharp_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1) :
    |Real.artanh x-(x+x^3/3)| ≤ x^5/(5*(1-x^2)) := by
  have hx2 : x^2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr (by rwa [abs_of_nonneg hx0])
  have hh := power_remainder_bound 4 hx0 (show 0 < 1-x^2 by linarith)
    (fun y hy => hasDerivAt_artanh_third (by rw [abs_of_nonneg hy.1]; exact hy.2.trans_lt hx))
    (fun y hy => segment_rational_bound hx hy 4)
  norm_num at hh ⊢
  exact hh

/-- A stronger atan estimate than the common denominator used in the paper. -/
theorem arctan_fifth_sharp_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |Real.arctan x-(x-x^3/3+x^5/5)| ≤ x^7/7 := by
  have hh := power_remainder_bound 6 hx (show (0 : ℝ) < 1 by norm_num)
    (fun y _ => hasDerivAt_arctan_fifth_remainder y)
    (fun y hy => by
      rw [abs_div, abs_neg, abs_pow, abs_of_nonneg hy.1,
        abs_of_nonneg (by positivity : 0 ≤ 1+y^2)]
      exact div_le_div_of_nonneg_left (pow_nonneg hy.1 _) (by norm_num)
        (by nlinarith [sq_nonneg y]))
  norm_num at hh ⊢
  exact hh

end TournamentHamiltonian
