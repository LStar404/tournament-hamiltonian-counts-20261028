module

public import TournamentHamiltonian.PeriodicBox.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

lemma integrable_complex_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℂ} (hf : Measurable f) {M : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ M) : Integrable f μ :=
  (integrable_const M).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

lemma complex_integral_re {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : Integrable f μ) :
    (∫ x, (f x).re ∂μ) = (∫ x, f x ∂μ).re := integral_re hf
lemma complex_integral_im {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : Integrable f μ) :
    (∫ x, (f x).im ∂μ) = (∫ x, f x ∂μ).im := integral_im hf

def complexPeriodic {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Prop :=
  ∀ x i, f (Function.update x i (x i + Real.pi)) = f x

def complexJoint {n : ℕ} (f : (Fin n → ℝ) → ℂ) : Prop :=
  ∀ x c, f (fun i => x i+c) = f x

lemma complex_boxes_eq {n : ℕ} (a b : ℝ) (f : (Fin n → ℝ) → ℂ)
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, ‖f x‖ ≤ M) (hp : complexPeriodic f) :
    (∫ x, f x ∂boxMeasure n a) = ∫ x, f x ∂boxMeasure n b := by
  have hi a := integrable_complex_bounded (boxMeasure n a) hf hb
  
  apply Complex.ext
  · rw [← complex_integral_re (hi a), ← complex_integral_re (hi b)]
    exact integral_boxes_eq a b _ (Complex.measurable_re.comp hf)
      (fun x => (Complex.abs_re_le_norm _).trans (hb x)) (fun x i => congrArg Complex.re (hp x i))
  · rw [← complex_integral_im (hi a), ← complex_integral_im (hi b)]
    exact integral_boxes_eq a b _ (Complex.measurable_im.comp hf)
      (fun x => (Complex.abs_im_le_norm _).trans (hb x)) (fun x i => congrArg Complex.im (hp x i))

/-- Ordinary Lebesgue gauge, not probability Haar. Both periodicity and joint invariance
are proved for the actual signed kernel before this lemma is used. -/
lemma complex_gauge {n : ℕ} (a : ℝ) (f : (Fin (n+1) → ℝ) → ℂ)
    (hf : Measurable f) {M : ℝ} (hb : ∀ x, ‖f x‖ ≤ M)
    (hp : complexPeriodic f) (hj : complexJoint f) :
    (∫ x, f x ∂boxMeasure (n+1) a) =
      (Real.pi : ℂ) * ∫ z, f (Fin.cons 0 z) ∂boxMeasure n a := by
  have hi := integrable_complex_bounded (boxMeasure (n+1) a) hf hb
  have hir := integrable_complex_bounded (boxMeasure n a) (hf.comp (by fun_prop))
    (fun z => hb (Fin.cons 0 z))
  change Integrable (fun z => f (Fin.cons 0 z)) (boxMeasure n a) at hir
  
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← complex_integral_re hi, ← complex_integral_re hir]
    exact gauge_root_zero a _ (Complex.measurable_re.comp hf)
      (fun x => (Complex.abs_re_le_norm _).trans (hb x))
      (fun x i => congrArg Complex.re (hp x i)) (fun x c => congrArg Complex.re (hj x c))
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [← complex_integral_im hi, ← complex_integral_im hir]
    exact gauge_root_zero a _ (Complex.measurable_im.comp hf)
      (fun x => (Complex.abs_im_le_norm _).trans (hb x))
      (fun x i => congrArg Complex.im (hp x i)) (fun x c => congrArg Complex.im (hj x c))

lemma integral_character_one (a : ℝ) (q : ℤ) :
    (∫ t, Complex.exp ((2 * (q : ℝ) * t : ℝ) * Complex.I) ∂cellMeasure a) =
      if q=0 then (Real.pi : ℂ) else 0 := by
  rw [show (∫ t, Complex.exp ((2 * (q : ℝ) * t : ℝ) * Complex.I) ∂cellMeasure a) =
      ∫ t in a..a+Real.pi, Complex.exp ((2 * (q : ℝ) * t : ℝ) * Complex.I) from by
        rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]; rfl]
  by_cases hq : q=0
  · simp [hq]
  · rw [ite_eq_right hq]
    have hc : (2 * (q : ℂ) * Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hq)) Complex.I_ne_zero
    have he (t : ℝ) : ((2 * (q : ℝ) * t : ℝ) : ℂ) * Complex.I =
        (2 * (q : ℂ) * Complex.I) * t := by push_cast; ring
    simp_rw [he]
    rw [integral_exp_mul_complex hc]
    have hp : Complex.exp ((2 * (q : ℂ) * Complex.I) * (a+Real.pi)) =
        Complex.exp ((2 * (q : ℂ) * Complex.I) * a) := by
      rw [show (2 * (q : ℂ) * Complex.I) * (a+Real.pi) =
        (2*(q : ℂ)*Complex.I)*a + (q : ℂ)*(2*Real.pi*Complex.I) by ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    push_cast
    rw [hp]
    simp

def character {m : ℕ} (q : Fin m → ℤ) (x : Fin m → ℝ) : ℂ :=
  ∏ i, Complex.exp ((2*(q i : ℝ)*x i : ℝ)*Complex.I)

lemma character_sum {m : ℕ} (q : Fin m → ℤ) (x : Fin m → ℝ) :
    character q x = Complex.exp ((2*(∑ i, (q i : ℝ)*x i) : ℝ)*Complex.I) := by
  rw [character, ← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma integral_character {m : ℕ} (a : ℝ) (q : Fin m → ℤ) :
    (∫ x, character q x ∂boxMeasure m a) = if q=0 then (Real.pi : ℂ)^m else 0 := by
  unfold character boxMeasure
  rw [integral_fintype_prod_eq_prod (fun (i : Fin m) (t : ℝ) =>
    Complex.exp ((2*(q i : ℝ)*t : ℝ)*Complex.I))]
  simp_rw [integral_character_one]
  by_cases hq : q=0
  · simp [hq]
  · rw [ite_eq_right hq]
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by simpa only [funext_iff, Pi.zero_apply, not_forall] using hq
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma character_continuous {m : ℕ} (q : Fin m → ℤ) : Continuous (character q) := by
  unfold character
  fun_prop
lemma character_norm {m : ℕ} (q : Fin m → ℤ) (x : Fin m → ℝ) : ‖character q x‖ = 1 := by
  unfold character
  rw [norm_prod]
  simp only [Complex.norm_exp_ofReal_mul_I, Finset.prod_const_one]
lemma character_integrable {m : ℕ} (q : Fin m → ℤ) (a : ℝ) :
    Integrable (character q) (boxMeasure m a) :=
  integrable_complex_bounded _ (character_continuous q).measurable
    (fun x => (character_norm q x).le)
lemma character_periodic {m : ℕ} (q : Fin m → ℤ) : complexPeriodic (character q) := by
  intro x i
  unfold character
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j=i
  · subst j
    simp only [Function.update_self]
    have he : ((2*(q i : ℝ)*(x i+Real.pi) : ℝ) : ℂ)*Complex.I =
        ((2*(q i : ℝ)*x i : ℝ) : ℂ)*Complex.I + (q i : ℂ)*(2*Real.pi*Complex.I) := by
      push_cast
      ring
    rw [he,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]
  · simp only [Function.update_of_ne h]
end RegularFourier
