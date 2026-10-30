module

public import TournamentHamiltonian.RegularFourier.Factorization

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation UniformBlowup
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Signed π-periodicity is guarded by odd order. Absolute-value periodicity alone
would not justify this theorem. -/
theorem signedKernel_periodic {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    complexPeriodic (signedKernel s ω) := by
  intro x i
  have h := centered_periodic (regularExponent k) (constrainedPolynomial s ω) x i
  simp_rw [regular_centered_factorization] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num) : (2:ℂ)^sᶜ.card ≠ 0) h

def rootIntegral {n : ℕ} (s : Finset (Edge (n+1))) (ω : Orientation (n+1)) : ℂ :=
  ∫ z, signedKernel s ω (Fin.cons 0 z) ∂boxMeasure n (-Real.pi/2)

lemma root_integrable {n : ℕ} (s : Finset (Edge (n+1))) (ω : Orientation (n+1)) :
    Integrable (fun z => signedKernel s ω (Fin.cons 0 z)) (boxMeasure n (-Real.pi/2)) :=
  integrable_complex_bounded _ ((signedKernel_continuous s ω).comp (by fun_prop)).measurable
    (fun z => signedKernel_norm_le s ω _)

lemma rootIntegral_closed {n : ℕ} (s : Finset (Edge (n+1))) (ω : Orientation (n+1)) :
    rootIntegral s ω = ∫ z in univ.pi (fun _ : Fin n => Icc (-Real.pi/2) (Real.pi/2)),
      signedKernel s ω (Fin.cons 0 z) := by
  simp only [rootIntegral,boxMeasure_eq_closed,show -Real.pi/2+Real.pi=Real.pi/2 by ring]

/-- Exact count/integral identity, retaining ordinary Lebesgue volume π^(m-1).
The number of unforced edge factors is sᶜ.card. -/
theorem coefficient_root_integral {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    (2:ℂ)^sᶜ.card * rootIntegral s ω =
      ((constrainedPolynomial s ω).coeff (regularExponent k) : ℂ)*(Real.pi:ℂ)^(2*k) := by
  have h := coefficient_integral (-Real.pi/2) (regularExponent k) (constrainedPolynomial s ω)
  simp_rw [regular_centered_factorization] at h
  rw [integral_const_mul, complex_gauge _ _ (signedKernel_continuous s ω).measurable
    (fun x => signedKernel_norm_le s ω x) (signedKernel_periodic s ω) (signedKernel_joint s ω)] at h
  change (2:ℂ)^sᶜ.card * ((Real.pi:ℂ)*rootIntegral s ω) = _ at h
  rw [pow_succ] at h
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  calc
    _ = (2:ℂ)^sᶜ.card*((Real.pi:ℂ)*rootIntegral s ω) := by ring
    _ = _ := h
    _ = _ := by ring

lemma rootIntegral_eq_real {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    rootIntegral s ω = (((constrainedPolynomial s ω).coeff (regularExponent k) : ℝ)*
      Real.pi^(2*k)/(2:ℝ)^sᶜ.card : ℝ) := by
  push_cast
  apply (eq_div_iff (pow_ne_zero _ (by norm_num) : (2:ℂ)^sᶜ.card ≠ 0)).mpr
  rw [mul_comm]
  exact coefficient_root_integral s ω

lemma rootIntegral_im {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    (rootIntegral s ω).im = 0 := by rw [rootIntegral_eq_real]; rfl
lemma rootIntegral_re {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    (rootIntegral s ω).re = ((constrainedPolynomial s ω).coeff (regularExponent k) : ℝ)*
      Real.pi^(2*k)/(2:ℝ)^sᶜ.card := by rw [rootIntegral_eq_real]; rfl
lemma rootIntegral_nonneg {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    0 ≤ (rootIntegral s ω).re := by rw [rootIntegral_re]; positivity

@[simp] lemma constrained_empty {m : ℕ} (ω : Orientation m) :
    constrainedPolynomial ∅ ω=orientationPolynomial m := by
  simp [constrainedPolynomial,orientationPolynomial]

lemma empty_rootIntegral_pos (k : ℕ) (ω : Orientation (2*k+1)) :
    0 < (rootIntegral ∅ ω).re := by
  rw [rootIntegral_re,constrained_empty]
  exact div_pos (mul_pos (regular_denominator_pos k) (pow_pos Real.pi_pos _)) (by positivity)

lemma edge_powers {m : ℕ} (s : Finset (Edge m)) :
    (2:ℝ)^sᶜ.card*(2:ℝ)^s.card=(2:ℝ)^(Fintype.card (Edge m)) := by
  rw [← pow_add,Finset.card_compl_add_card]

/-- The true uniform-regular probability. The factor 2^(-a) is indispensable;
this is not the probability of regularity after conditioning independent bits. -/
theorem regularProbability_integral {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    regularProbability s ω = ((2:ℝ)^s.card)⁻¹ *
      (rootIntegral s ω).re/(rootIntegral ∅ ω).re := by
  rw [regularProbability_eq_coeff_ratio, rootIntegral_re, rootIntegral_re, constrained_empty]
  simp only [Finset.compl_empty, Finset.card_univ]
  have hd := (regular_denominator_pos k).ne'
  have hp : Real.pi^(2*k) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hs : (2:ℝ)^s.card ≠ 0 := by positivity
  have ht : (2:ℝ)^sᶜ.card ≠ 0 := by positivity
  have hn : (2:ℝ)^(Fintype.card (Edge (2*k+1))) ≠ 0 := by positivity
  have he := edge_powers s
  field_simp
  nlinarith

/-- Independent-bit regular sample rate: total regular counts divided by 2^N. -/
theorem regular_sample_rate (k : ℕ) (ω : Orientation (2*k+1)) :
    ((orientationPolynomial (2*k+1)).coeff (regularExponent k) : ℝ)/
      (2:ℝ)^(Fintype.card (Edge (2*k+1))) = (rootIntegral ∅ ω).re/Real.pi^(2*k) := by
  rw [rootIntegral_re,constrained_empty]
  simp only [Finset.compl_empty,Finset.card_univ]
  field_simp

/-- Independent-bit joint rate of the forced arcs AND regularity. -/
theorem joint_sample_rate {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    ((constrainedPolynomial s ω).coeff (regularExponent k) : ℝ)/
      (2:ℝ)^(Fintype.card (Edge (2*k+1))) =
      ((2:ℝ)^s.card)⁻¹*(rootIntegral s ω).re/Real.pi^(2*k) := by
  rw [rootIntegral_re]
  have he := edge_powers s
  field_simp
  nlinarith

/-- Independent-bit regularity rate AFTER fixing the prescribed arcs; the sample
space has 2^(N-a) completions, not the number of regular tournaments. -/
theorem forced_sample_rate {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    ((constrainedPolynomial s ω).coeff (regularExponent k) : ℝ)/(2:ℝ)^sᶜ.card =
      (rootIntegral s ω).re/Real.pi^(2*k) := by
  rw [rootIntegral_re]
  field_simp

end RegularFourier
