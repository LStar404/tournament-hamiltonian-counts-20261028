module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace ForestGaussian

/-- A deliberately elementary scalar bound: no power-series or asymptotic premise. -/
theorem log_one_sub_remainder (x : ℝ) (_hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    0 ≤ -Real.log (1 - x) - x ∧
      -Real.log (1 - x) - x ≤ 2 * x ^ 2 := by
  have hp : 0 < 1 - x := by linarith
  have hu := Real.log_le_sub_one_of_pos hp
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hl
  have he : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  rw [he] at hl
  have hd : x / (1 - x) - x = x ^ 2 / (1 - x) := by field_simp; ring
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg x)
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 1 / 2 ≤ 1 - x)
  norm_num at hdiv
  constructor
  · linarith
  · linarith

/-- Reciprocal error on the same half interval. -/
theorem inv_one_sub_remainder (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    0 ≤ (1 - x)⁻¹ - 1 ∧ (1 - x)⁻¹ - 1 ≤ 2 * x := by
  have hp : 0 < 1 - x := by linarith
  have he : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp; ring
  rw [he]
  constructor
  · positivity
  · have hd := div_le_div_of_nonneg_left hx (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith : 1 / 2 ≤ 1 - x)
    norm_num at hd
    linarith

/-- The logarithm of the diagonalized finite Gaussian determinant--phase factor. -/
noncomputable def spectralLogFactor {ι : Type*} [Fintype ι]
    (m : ℝ) (l c : ι → ℝ) : ℝ :=
  ∑ i, (-Real.log (1 - l i / m) / 2 - c i / (2 * m * (1 - l i / m)))

/-- The actual positive scalar factor, before identifying a matrix eigenbasis. -/
noncomputable def spectralFactor {ι : Type*} [Fintype ι]
    (m : ℝ) (l c : ι → ℝ) : ℝ :=
  (∏ i, (Real.sqrt (1 - l i / m))⁻¹) *
    Real.exp (-(∑ i, c i / (1 - l i / m)) / (2 * m))

theorem spectralFactor_pos {ι : Type*} [Fintype ι]
    (m : ℝ) (l c : ι → ℝ) (hm : 8 ≤ m) (hl : ∀ i, l i ≤ 4) :
    0 < spectralFactor m l c := by
  apply mul_pos _ (Real.exp_pos _)
  apply Finset.prod_pos
  intro i _
  apply inv_pos.mpr
  apply Real.sqrt_pos.mpr
  have hmpos : 0 < m := by linarith
  have hdiv : l i / m ≤ 1 / 2 := (div_le_iff₀ hmpos).mpr (by linarith [hl i])
  linarith

theorem log_spectralFactor {ι : Type*} [Fintype ι]
    (m : ℝ) (l c : ι → ℝ) (hm : 8 ≤ m) (hl : ∀ i, l i ≤ 4) :
    Real.log (spectralFactor m l c) = spectralLogFactor m l c := by
  have hp (i : ι) : 0 < 1 - l i / m := by
    have hmpos : 0 < m := by linarith
    have hdiv : l i / m ≤ 1 / 2 := (div_le_iff₀ hmpos).mpr (by linarith [hl i])
    linarith
  unfold spectralFactor spectralLogFactor
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr (fun i _ =>
    inv_ne_zero (Real.sqrt_pos.mpr (hp i)).ne')) (Real.exp_ne_zero _), Real.log_exp,
    Real.log_prod (fun i _ => inv_ne_zero (Real.sqrt_pos.mpr (hp i)).ne')]
  simp_rw [Real.log_inv, Real.log_sqrt (hp _).le]
  rw [Finset.sum_sub_distrib, neg_div, ← sub_eq_add_neg]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_div]
    congr 1
    ring

/-- Uniform diagonal spectral estimate. The hypotheses are finite spectral budgets,
not an assumption of the asserted error. Matrix applications must derive these budgets. -/
theorem spectralLogFactor_error {ι : Type*} [Fintype ι]
    (m a s : ℝ) (l c : ι → ℝ) (hm : 8 ≤ m)
    (hl0 : ∀ i, 0 ≤ l i) (hl4 : ∀ i, l i ≤ 4)
    (hc : ∀ i, 0 ≤ c i)
    (htrace : ∑ i, l i = 2 * a)
    (hsquare : ∑ i, l i ^ 2 ≤ 8 * a)
    (hphase : ∑ i, c i = 2 * s) :
    |spectralLogFactor m l c - (a - s) / m| ≤ 8 * (a + s) / m ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hmne : m ≠ 0 := hmpos.ne'
  have hx0 (i : ι) : 0 ≤ l i / m := div_nonneg (hl0 i) hmpos.le
  have hxhalf (i : ι) : l i / m ≤ 1 / 2 :=
    (div_le_iff₀ hmpos).mpr (by linarith [hl4 i])
  let d : ι → ℝ := fun i => (-Real.log (1 - l i / m) - l i / m) / 2
  let p : ι → ℝ := fun i => c i / (2 * m) * ((1 - l i / m)⁻¹ - 1)
  have hd0 (i : ι) : 0 ≤ d i :=
    div_nonneg (log_one_sub_remainder _ (hx0 i) (hxhalf i)).1 (by norm_num)
  have hdup (i : ι) : d i ≤ (l i) ^ 2 / m ^ 2 := by
    have h := (log_one_sub_remainder _ (hx0 i) (hxhalf i)).2
    dsimp [d]
    rw [div_pow] at h
    linarith
  have hp0 (i : ι) : 0 ≤ p i := by
    exact mul_nonneg (div_nonneg (hc i) (by positivity))
      (inv_one_sub_remainder _ (hx0 i) (hxhalf i)).1
  have hpup (i : ι) : p i ≤ 4 * c i / m ^ 2 := by
    have h1 := (inv_one_sub_remainder _ (hx0 i) (hxhalf i)).2
    have h2 : 2 * (l i / m) ≤ 8 / m := by
      apply (le_div_iff₀ hmpos).mpr
      field_simp at *
      linarith [hl4 i]
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2)
      (show 0 ≤ c i / (2 * m) from div_nonneg (hc i) (by positivity))
    dsimp [p]
    convert h3 using 1; field_simp; ring
  have hd : (∑ i, d i) ≤ 8 * a / m ^ 2 := by
    calc
      _ ≤ ∑ i, (l i) ^ 2 / m ^ 2 := Finset.sum_le_sum (fun i _ => hdup i)
      _ = (∑ i, (l i) ^ 2) / m ^ 2 := (Finset.sum_div ..).symm
      _ ≤ _ := div_le_div_of_nonneg_right hsquare (sq_nonneg m)
  have hp : (∑ i, p i) ≤ 8 * s / m ^ 2 := by
    calc
      _ ≤ ∑ i, 4 * c i / m ^ 2 := Finset.sum_le_sum (fun i _ => hpup i)
      _ = 8 * s / m ^ 2 := by rw [← Finset.sum_div, ← Finset.mul_sum, hphase]; ring
  have he : spectralLogFactor m l c - (a - s) / m = (∑ i, d i) - ∑ i, p i := by
    have hf (i : ι) :
        -Real.log (1 - l i / m) / 2 - c i / (2 * m * (1 - l i / m)) =
          d i - p i + (l i - c i) / (2 * m) := by
      dsimp [d, p]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    unfold spectralLogFactor
    simp_rw [hf]
    have hlin : (∑ i, (l i - c i) / (2 * m)) = (a - s) / m := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, htrace, hphase]
      ring
    rw [Finset.sum_add_distrib, hlin, Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ |∑ i, d i| + |∑ i, p i| := abs_sub _ _
    _ = (∑ i, d i) + ∑ i, p i := by
      rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => hd0 i)),
        abs_of_nonneg (Finset.sum_nonneg (fun i _ => hp0 i))]
    _ ≤ 8 * a / m ^ 2 + 8 * s / m ^ 2 := add_le_add hd hp
    _ = _ := by ring

/-- Spectral square budget follows from the genuine nonnegative spectral interval. -/
theorem spectral_square_budget {ι : Type*} [Fintype ι]
    (a : ℝ) (l : ι → ℝ) (hl0 : ∀ i, 0 ≤ l i) (hl4 : ∀ i, l i ≤ 4)
    (htrace : ∑ i, l i = 2 * a) : ∑ i, l i ^ 2 ≤ 8 * a := by
  calc
    _ ≤ ∑ i, 4 * l i := Finset.sum_le_sum (fun i _ => by nlinarith [hl0 i, hl4 i])
    _ = _ := by rw [← Finset.mul_sum, htrace]; ring

/-- The positive product determinant--phase expression satisfies the same error bound. -/
theorem spectralFactor_log_error {ι : Type*} [Fintype ι]
    (m a s : ℝ) (l c : ι → ℝ) (hm : 8 ≤ m)
    (hl0 : ∀ i, 0 ≤ l i) (hl4 : ∀ i, l i ≤ 4)
    (hc : ∀ i, 0 ≤ c i) (htrace : ∑ i, l i = 2 * a)
    (hphase : ∑ i, c i = 2 * s) :
    |Real.log (spectralFactor m l c) - (a - s) / m| ≤ 8 * (a + s) / m ^ 2 := by
  rw [log_spectralFactor m l c hm hl4]
  exact spectralLogFactor_error m a s l c hm hl0 hl4 hc htrace
    (spectral_square_budget a l hl0 hl4 htrace) hphase

/-- A dimension-only corollary, uniform in all spectral data with a,s ≤ m. -/
theorem spectralFactor_log_error_uniform {ι : Type*} [Fintype ι]
    (m a s : ℝ) (l c : ι → ℝ) (hm : 8 ≤ m)
    (hl0 : ∀ i, 0 ≤ l i) (hl4 : ∀ i, l i ≤ 4)
    (hc : ∀ i, 0 ≤ c i) (htrace : ∑ i, l i = 2 * a)
    (hphase : ∑ i, c i = 2 * s) (ha : a ≤ m) (hs : s ≤ m) :
    |Real.log (spectralFactor m l c) - (a - s) / m| ≤ 16 / m := by
  have hmpos : 0 < m := by linarith
  apply (spectralFactor_log_error m a s l c hm hl0 hl4 hc htrace hphase).trans
  calc
    _ ≤ 8 * (m + m) / m ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg m)
      linarith
    _ = _ := by field_simp; ring

end ForestGaussian
