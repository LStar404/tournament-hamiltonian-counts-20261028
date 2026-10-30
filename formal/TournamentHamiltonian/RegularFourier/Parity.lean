module

public import TournamentHamiltonian.RegularFourier.Rates
public import TournamentHamiltonian.RegularOrientation.Boundary

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation UniformBlowup
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

lemma evaluation_periodic {m : ℕ} (p : MvPolynomial (Fin m) ℕ) : complexPeriodic (evaluation p) := by
  intro x i
  have h := centered_periodic (0 : Exponent m) p x i
  simpa only [centeredEvaluation,Finsupp.zero_apply,Nat.cast_zero,zero_mul,mul_zero,Finset.sum_const_zero,
    Complex.ofReal_zero,Complex.exp_zero,one_mul] using h

lemma cis_nat_pi (n : ℕ) : cis ((n:ℝ)*Real.pi)=(-1:ℂ)^n := by
  unfold cis
  push_cast
  rw [mul_assoc,Complex.exp_nat_mul,Complex.exp_pi_mul_I]

lemma sum_update_pi {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    (∑ j,Function.update x i (x i+Real.pi) j)=(∑ j,x j)+Real.pi := by
  have he : Function.update x i (x i+Real.pi) = fun j => x j+(if j=i then Real.pi else 0) := by
    ext j
    by_cases h : j=i <;> simp [h,Function.update_of_ne]
  rw [he,Finset.sum_add_distrib]
  simp

/-- Exact signed coordinate anti/periodicity at EVERY order. For positive even order
the sign is negative, so π-gauge cannot be borrowed from the absolute kernel. -/
theorem signedKernel_pi_shift {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m)
    (x : Fin m → ℝ) (i : Fin m) :
    signedKernel s ω (Function.update x i (x i+Real.pi)) =
      (-1:ℂ)^(m-1)*signedKernel s ω x := by
  have hm : 1≤m := by have := i.isLt; omega
  have hcast : (m:ℝ)-1=((m-1:ℕ):ℝ) := by rw [Nat.cast_sub hm,Nat.cast_one]
  have h := evaluation_periodic (constrainedPolynomial s ω) x i
  rw [evaluation_factorization,evaluation_factorization,sum_update_pi,mul_add,cis_add] at h
  rw [hcast,cis_nat_pi] at h
  have ha : (2:ℂ)^sᶜ.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have hc := cis_ne_zero (((m-1:ℕ):ℝ)*(∑ j,x j))
  have he : (-1:ℂ)^(m-1)*signedKernel s ω (Function.update x i (x i+Real.pi)) =
      signedKernel s ω x := by
    apply mul_left_cancel₀ hc
    apply mul_left_cancel₀ ha
    calc
      _ = (2:ℂ)^sᶜ.card*(cis (((m-1:ℕ):ℝ)*(∑ j,x j))*(-1:ℂ)^(m-1))*
        signedKernel s ω (Function.update x i (x i+Real.pi)) := by ring
      _ = _ := h
      _ = _ := by ring
  have hs : (-1:ℂ)^(m-1)*(-1:ℂ)^(m-1)=1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1:ℂ)^(m-1)*(-1:ℂ)^(m-1))*signedKernel s ω (Function.update x i (x i+Real.pi)) := by rw [hs,one_mul]
    _ = _ := by rw [mul_assoc,he]

/-- Even positive orders have no genuine regular sample space. This does not say
that a signed π-cell integral is zero; the explicit order-two counterexample is separate. -/
lemma even_no_regular {m : ℕ} (hm : 0<m) (he : Even m) :
    ¬ Nonempty (RegularTournament m) := no_regular_positive_even hm he

end RegularFourier
