module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

namespace TournamentHamiltonian

/-- The derivative used in the positive-frequency comparison is computed from
actual sine and cosine, not supplied as a hypothesis. -/
theorem hasDerivAt_mul_cot {x : ℝ} (hx : Real.sin x ≠ 0) :
    HasDerivAt (fun y : ℝ => y * Real.cot y)
      ((Real.sin x * Real.cos x - x) / Real.sin x ^ 2) x := by
  simp_rw [Real.cot_eq_cos_div_sin]
  convert (hasDerivAt_id x).mul ((Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx) using 1
  · funext y
    simp [div_eq_mul_inv]
  · dsimp
    field_simp [hx]
    linear_combination x * (Real.sin_sq_add_cos_sq x)


/-- The scalar monotonicity behind the carousel's nested positive frequencies. -/
theorem mul_cot_strictAntiOn :
    StrictAntiOn (fun x : ℝ => x * Real.cot x) (Set.Ioo 0 (Real.pi / 2)) := by
  have hd (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) :=
    hasDerivAt_mul_cot (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2, Real.pi_pos])).ne'
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 (Real.pi / 2))
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo 0 (Real.pi / 2) := by simpa only [interior_Ioo] using hx
    rw [(hd x hx').deriv]
    apply div_neg_of_neg_of_pos
    · have hs := Real.sin_lt (show 0 < 2 * x by linarith [hx'.1])
      rw [Real.sin_two_mul] at hs
      linarith
    · exact sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hx'.1 (by linarith [hx'.2, Real.pi_pos]))

/-- At fixed positive frequency index, increasing the order strictly increases
`cot (c / d) / d` while its angle remains in the positive half-period. -/
theorem normalized_cot_strictMono {c d e : ℝ} (hc : 0 < c)
    (hd : 0 < d) (hde : d < e) (hangle : c / d < Real.pi / 2) :
    Real.cot (c / d) / d < Real.cot (c / e) / e := by
  have he : 0 < e := hd.trans hde
  have hcd : 0 < c / d := div_pos hc hd
  have hce : 0 < c / e := div_pos hc he
  have hlt : c / e < c / d := div_lt_div_of_pos_left hc hd hde
  have hmono := mul_cot_strictAntiOn
    (show c / e ∈ Set.Ioo 0 (Real.pi / 2) from ⟨hce, hlt.trans hangle⟩)
    (show c / d ∈ Set.Ioo 0 (Real.pi / 2) from ⟨hcd, hangle⟩) hlt
  have hrewrite (a : ℝ) : (c / a) * Real.cot (c / a) = c * (Real.cot (c / a) / a) := by ring
  dsimp only at hmono
  rw [hrewrite d, hrewrite e] at hmono
  exact (mul_lt_mul_iff_right₀ hc).mp hmono

/-- Strict cotangent positivity in its positive half-period. -/
theorem cot_pos_half_period {x : ℝ} (hx : 0 < x) (hxp : x < Real.pi / 2) :
    0 < Real.cot x := by
  rw [Real.cot_eq_cos_div_sin]
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxp⟩)
    (Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos]))

/-- `x cot x < 1` supplies a uniform strict bound on every normalized frequency. -/
theorem mul_cot_lt_one {x : ℝ} (hx : 0 < x) (hxp : x < Real.pi / 2) :
    x * Real.cot x < 1 := by
  have hcos := Real.cos_pos_of_mem_Ioo (show x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
    from ⟨by linarith [Real.pi_pos], hxp⟩)
  have hsin := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have htan := Real.lt_tan hx hxp
  rw [Real.tan_eq_sin_div_cos] at htan
  rw [Real.cot_eq_cos_div_sin, ← mul_div_assoc, div_lt_one hsin]
  exact (lt_div_iff₀ hcos).mp htan

/-- The manuscript's positive frequencies, indexed from zero. The corresponding
odd order is `2 * m + 1`. -/
noncomputable def carouselPositiveFrequency (m : ℕ) (j : Fin m) : ℝ :=
  Real.cot ((2 * (j.val : ℝ) + 1) * Real.pi / (2 * (2 * (m : ℝ) + 1))) /
    (2 * (m : ℝ) + 1)

theorem carouselPositiveAngle_mem (m : ℕ) (j : Fin m) :
    (2 * (j.val : ℝ) + 1) * Real.pi / (2 * (2 * (m : ℝ) + 1)) ∈
      Set.Ioo 0 (Real.pi / 2) := by
  have hj : (j.val : ℝ) < m := by exact_mod_cast j.isLt
  have hm : (0 : ℝ) ≤ m := by positivity
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (2 * (m : ℝ) + 1))).mpr
    nlinarith [mul_lt_mul_of_pos_right hj Real.pi_pos]

theorem carouselPositiveFrequency_pos (m : ℕ) (j : Fin m) :
    0 < carouselPositiveFrequency m j := by
  unfold carouselPositiveFrequency
  have ha := carouselPositiveAngle_mem m j
  exact div_pos (cot_pos_half_period ha.1 ha.2) (by positivity)

theorem carouselPositiveFrequency_lt_one (m : ℕ) (j : Fin m) :
    carouselPositiveFrequency m j < 1 := by
  have ha := carouselPositiveAngle_mem m j
  have hh := mul_cot_lt_one ha.1 ha.2
  have hc : 1 ≤ (2 * (j.val : ℝ) + 1) * Real.pi / 2 := by
    have hj : (0 : ℝ) ≤ j.val := by positivity
    nlinarith [Real.one_le_pi_div_two, Real.pi_pos]
  have heq :
      ((2 * (j.val : ℝ) + 1) * Real.pi / (2 * (2 * (m : ℝ) + 1))) *
        Real.cot ((2 * (j.val : ℝ) + 1) * Real.pi / (2 * (2 * (m : ℝ) + 1))) =
      ((2 * (j.val : ℝ) + 1) * Real.pi / 2) * carouselPositiveFrequency m j := by
    simp only [carouselPositiveFrequency, ← div_div]
    ring
  rw [heq] at hh
  exact (le_mul_of_one_le_left (carouselPositiveFrequency_pos m j).le hc).trans_lt hh

theorem carouselPositiveFrequency_strictMono {m k : ℕ} (hmk : m < k) (j : Fin m) :
    carouselPositiveFrequency m j <
      carouselPositiveFrequency k (j.castLT (j.isLt.trans hmk)) := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hmkR : (m : ℝ) < k := by exact_mod_cast hmk
  have hc : 0 < (2 * (j.val : ℝ) + 1) * Real.pi / 2 := by positivity
  have hangle : ((2 * (j.val : ℝ) + 1) * Real.pi / 2) / (2 * (m : ℝ) + 1) <
      Real.pi / 2 := by
    simpa only [div_div] using (carouselPositiveAngle_mem m j).2
  have hh := normalized_cot_strictMono hc (by positivity : (0 : ℝ) < 2 * (m : ℝ) + 1)
    (show 2 * (m : ℝ) + 1 < 2 * (k : ℝ) + 1 by linarith) hangle
  simpa [carouselPositiveFrequency, div_div] using hh

end TournamentHamiltonian
