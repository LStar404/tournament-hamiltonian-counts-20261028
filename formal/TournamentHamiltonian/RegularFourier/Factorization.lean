module

public import TournamentHamiltonian.RegularFourier.Polynomial

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation UniformBlowup
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def cis (t : ℝ) : ℂ := Complex.exp ((t : ℂ)*Complex.I)
lemma cis_add (u v : ℝ) : cis (u+v)=cis u*cis v := by
  simp only [cis, Complex.ofReal_add, add_mul, Complex.exp_add]
@[simp] lemma cis_zero : cis 0=1 := by simp [cis]
lemma cis_norm (t : ℝ) : ‖cis t‖=1 := Complex.norm_exp_ofReal_mul_I t
lemma cis_ne_zero (t : ℝ) : cis t ≠ 0 := Complex.exp_ne_zero _
lemma cis_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) : cis (∑ i∈s,f i)=∏ i∈s,cis (f i) := by
  simp only [cis, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
lemma cis_add_neg (t : ℝ) : cis t+cis (-t)=2*(Real.cos t : ℂ) := by
  simp only [cis, Complex.ofReal_neg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos]
  ring
lemma cosine_factor (u v : ℝ) : cis (2*u)+cis (2*v)=2*cis (u+v)*(Real.cos (u-v):ℂ) := by
  have h1 : cis (2*u)=cis (u+v)*cis (u-v) := by rw [← cis_add]; congr 1; ring
  have h2 : cis (2*v)=cis (u+v)*cis (-(u-v)) := by rw [← cis_add]; congr 1; ring
  rw [h1,h2,← mul_add,cis_add_neg]
  ring

lemma edge_sum {m : ℕ} (f : Fin m → Fin m → ℝ) :
    (∑ e : Edge m, f e.val.1 e.val.2) = ∑ i, ∑ j, if i < j then f i j else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin m × Fin m => p.1<p.2))
    (by simp) (fun p => f p.1 p.2)]
  simp only [Finset.sum_filter]
  exact Fintype.sum_prod_type _

/-- Every canonical edge contributes each endpoint once. This fixes the direction and
centering factor against the actual polynomial, rather than only checking sum b=0. -/
lemma endpoint_sum {m : ℕ} (x : Fin m → ℝ) :
    (∑ e : Edge m, (x e.val.1+x e.val.2)) = ((m : ℝ)-1)*(∑ i,x i) := by
  rw [edge_sum (fun i j => x i+x j)]
  have hp (i j : Fin m) : (if i < j then x i+x j else 0) =
      (if i < j then x i else 0)+(if i < j then x j else 0) := by split_ifs <;> simp
  simp_rw [hp, Finset.sum_add_distrib]
  have hs : (∑ i,∑ j,if i < j then x j else 0) = ∑ i,∑ j,if j < i then x i else 0 := by
    rw [Finset.sum_comm]
  rw [hs, ← Finset.sum_add_distrib]
  have hi (i : Fin m) : (∑ j, if i < j then x i else 0)+(∑ j,if j < i then x i else 0) =
      ((m : ℝ)-1)*x i := by
    rw [← Finset.sum_add_distrib]
    have hh (j : Fin m) : (if i < j then x i else 0)+(if j < i then x i else 0) =
        if j=i then 0 else x i := by
      rcases lt_trichotomy i j with h|h|h
      · simp [h, not_lt_of_ge h.le, ne_of_gt h]
      · simp [h]
      · simp [h, not_lt_of_ge h.le, ne_of_lt h]
    simp_rw [hh]
    have hc (j : Fin m) : (if j=i then (0:ℝ) else x i) = x i-(if j=i then x i else 0) := by
      split_ifs <;> simp
    simp_rw [hc]
    simp [Finset.sum_sub_distrib]
    ring
  simp_rw [hi]
  rw [Finset.mul_sum]

def signedFactor {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m)
    (x : Fin m → ℝ) (e : Edge m) : ℂ :=
  if e∈s then cis (x (winner ω e)-x (loser ω e)) else (Real.cos (x e.val.1-x e.val.2):ℂ)

def signedKernel {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) (x : Fin m → ℝ) : ℂ :=
  ∏ e, signedFactor s ω x e

lemma signedKernel_continuous {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) :
    Continuous (signedKernel s ω) := by
  unfold signedKernel
  apply continuous_finsetProd _
  intro e _
  unfold signedFactor
  split_ifs
  · unfold cis
    fun_prop
  · fun_prop

lemma signedFactor_norm_le {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m)
    (x : Fin m → ℝ) (e : Edge m) : ‖signedFactor s ω x e‖ ≤ 1 := by
  by_cases he : e∈s
  · simp only [signedFactor, he, ite_true, cis_norm, le_refl]
  · simpa only [signedFactor, he, ite_false, Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one _
lemma signedKernel_norm_le {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m)
    (x : Fin m → ℝ) : ‖signedKernel s ω x‖ ≤ 1 := by
  rw [signedKernel, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun e _ => signedFactor_norm_le s ω x e)

lemma signedKernel_joint {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) :
    complexJoint (signedKernel s ω) := by
  intro x c
  unfold signedKernel signedFactor
  apply Finset.prod_congr rfl
  intro e _
  simp only [add_sub_add_right_eq_sub]

lemma forced_factor {m : ℕ} (ω : Orientation m) (x : Fin m → ℝ) (e : Edge m) :
    cis (2*x (winner ω e))=cis (x e.val.1+x e.val.2)*cis (x (winner ω e)-x (loser ω e)) := by
  rw [← cis_add]
  congr 1
  cases h : ω e <;> simp [winner,loser,h] <;> ring

lemma evaluation_factorization {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m)
    (x : Fin m → ℝ) :
    evaluation (constrainedPolynomial s ω) x =
      (2:ℂ)^sᶜ.card * cis (((m:ℝ)-1)*(∑ i,x i))*signedKernel s ω x := by
  unfold evaluation constrainedPolynomial
  rw [eval₂_prod]
  have he (e : Edge m) :
      eval₂ (Nat.castRingHom ℂ) (fun i => Complex.exp ((2*x i : ℝ)*Complex.I))
        (if e∈s then X (winner ω e) else X e.val.1+X e.val.2) =
      (if e∈s then (1:ℂ) else 2)*cis (x e.val.1+x e.val.2)*signedFactor s ω x e := by
    by_cases h : e∈s
    · simp only [h,ite_true,eval₂_X,signedFactor,one_mul]
      exact forced_factor ω x e
    · simp only [h,ite_false,eval₂_add,eval₂_X,signedFactor]
      exact cosine_factor _ _
  simp_rw [he,Finset.prod_mul_distrib]
  have hc : (∏ e : Edge m, if e∈s then (1:ℂ) else 2)=(2:ℂ)^sᶜ.card := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 2
    ext e
    simp
  rw [hc, ← cis_sum,endpoint_sum]
  rfl

lemma regular_centered_factorization {k : ℕ} (s : Finset (Edge (2*k+1)))
    (ω : Orientation (2*k+1)) (x : Fin (2*k+1) → ℝ) :
    centeredEvaluation (regularExponent k) (constrainedPolynomial s ω) x =
      (2:ℂ)^sᶜ.card*signedKernel s ω x := by
  rw [centeredEvaluation,evaluation_factorization]
  have he : (∑ i, ((regularExponent k) i : ℝ)*x i) = (k:ℝ)*(∑ i,x i) := by
    simp [regularExponent, Finset.mul_sum]
  rw [he]
  change cis (-2*((k:ℝ)*(∑ i,x i)))*((2:ℂ)^sᶜ.card*cis (_)*signedKernel s ω x)=_
  have hz : -2*((k:ℝ)*(∑ i,x i))+(((2*k+1:ℕ):ℝ)-1)*(∑ i,x i)=0 := by push_cast; ring
  calc
    _ = (2:ℂ)^sᶜ.card * (cis (-2*((k:ℝ)*(∑ i,x i))) *
        cis ((((2*k+1:ℕ):ℝ)-1)*(∑ i,x i))) * signedKernel s ω x := by ring
    _ = _ := by rw [← cis_add,hz,cis_zero,mul_one]

end RegularFourier
