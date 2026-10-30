module

public import TournamentHamiltonian.UniformTorusTail.Subsets

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace UniformTorusTail
open MeasureTheory Set Function PeriodicBox TorusCluster RootGaussianTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {m n : ℕ}

def farConstant (m : ℕ) : ℝ := Real.exp (-kappa0*(m : ℝ)^2/128)

def outlierSets (m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun B => 0 < B.card ∧ (B.card : ℝ) < (m : ℝ)/4)

def outlierTerm (H : SimpleGraph (Fin m)) (B : Finset (Fin m)) (c : ℝ)
    (x : Fin m → ℝ) : ℝ :=
  Real.exp (-kappa1*(m : ℝ)*B.card/2) *
    (arcEvent Bᶜ c localRadius).indicator (fun x => insideProduct H x Bᶜ) x

def localTerm (H : SimpleGraph (Fin (n+1))) (t c : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  (arcEvent Finset.univ c localRadius).indicator (badKernel H 0 t) x

def centerMajorant (H : SimpleGraph (Fin (n+1))) (t c : ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  farConstant (n+1) + (∑ B ∈ outlierSets (n+1), outlierTerm H B c x) + localTerm H t c x

lemma badKernel_nonneg (H : SimpleGraph (Fin m)) (root : Fin m) (t : ℝ) (x : Fin m → ℝ) :
    0 ≤ badKernel H root t x := Set.indicator_nonneg (fun x _ => kernel_nonneg H x) x

lemma badKernel_le_kernel (H : SimpleGraph (Fin m)) (root : Fin m) (t : ℝ) (x : Fin m → ℝ) :
    badKernel H root t x ≤ kernel H x := by
  by_cases hx : x ∈ rootBad root t
  · simp [badKernel,hx]
  · simp [badKernel,hx,kernel_nonneg H x]

lemma outlierTerm_nonneg (H : SimpleGraph (Fin m)) (B : Finset (Fin m)) (c : ℝ) (x : Fin m → ℝ) :
    0 ≤ outlierTerm H B c x :=
  mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun x _ => insideProduct_nonneg H x Bᶜ) x)

lemma localTerm_nonneg (H : SimpleGraph (Fin (n+1))) (t c : ℝ) (x : Fin (n+1) → ℝ) :
    0 ≤ localTerm H t c x := Set.indicator_nonneg (fun x _ => badKernel_nonneg H 0 t x) x

lemma centerMajorant_nonneg (H : SimpleGraph (Fin (n+1))) (t c : ℝ) (x : Fin (n+1) → ℝ) :
    0 ≤ centerMajorant H t c x :=
  add_nonneg (add_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg (fun B _ => outlierTerm_nonneg H B c x))) (localTerm_nonneg H t c x)

/-- Exhaustive actual-configuration domination, using only sixteen fixed centers. -/
theorem full_pointwise_majorant (H : SimpleGraph (Fin (n+1)))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 64 ≤ n+1) (t : ℝ) (x : Fin (n+1) → ℝ) :
    badKernel H 0 t x ≤ ∑ j : Fin 16, centerMajorant H t (center j) x := by
  obtain ⟨j,hj,hcase⟩ := three_region_cover x
  have hc : badKernel H 0 t x ≤ centerMajorant H t (center j) x := by
    have hfar : 0 ≤ farConstant (n+1) := (Real.exp_pos _).le
    have hout : 0 ≤ ∑ B ∈ outlierSets (n+1), outlierTerm H B (center j) x :=
      Finset.sum_nonneg (fun B _ => outlierTerm_nonneg H B (center j) x)
    have hlocal := localTerm_nonneg H t (center j) x
    rcases hcase with hf | ⟨hf,hb⟩ | hb
    · have h := (badKernel_le_kernel H 0 t x).trans (far_kernel_bound H hdegree hm x _ hj hf)
      change badKernel H 0 t x ≤ farConstant (n+1) at h
      unfold centerMajorant
      linarith
    · let B := outliers x (center j)
      have hB : B ∈ outlierSets (n+1) := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb,
          outliers_lt_quarter_of_not_far x _ hf⟩
      have hcomp : Bᶜ = outer x (center j) := by simp [B,outliers]
      have harc : x ∈ arcEvent Bᶜ (center j) localRadius := by
        rw [arcEvent_iff_subset_arc, hcomp]
        exact Finset.Subset.refl _
      have he : outlierTerm H B (center j) x =
          Real.exp (-kappa1*((n+1 : ℕ) : ℝ)*(outliers x (center j)).card/2) *
            insideProduct H x (outer x (center j)) := by
        rw [outlierTerm,Set.indicator_of_mem harc,hcomp]
      have h := (badKernel_le_kernel H 0 t x).trans (outlier_kernel_bound H hdegree hm x _ hf)
      rw [← he] at h
      have hs : outlierTerm H B (center j) x ≤
          ∑ A ∈ outlierSets (n+1), outlierTerm H A (center j) x :=
        Finset.single_le_sum (fun A _ => outlierTerm_nonneg H A (center j) x) hB
      unfold centerMajorant
      linarith
    · have harc : x ∈ arcEvent Finset.univ (center j) localRadius := by
        apply (arcEvent_univ_iff_no_outliers (center j) x).mpr
        exact Finset.card_eq_zero.mp hb
      have he : localTerm H t (center j) x = badKernel H 0 t x := Set.indicator_of_mem harc _
      unfold centerMajorant
      linarith
  exact hc.trans (Finset.single_le_sum (fun k _ => centerMajorant_nonneg H t (center k) x)
    (Finset.mem_univ j))

lemma outlierTerm_integrable (H : SimpleGraph (Fin m)) (B : Finset (Fin m)) (c : ℝ) :
    Integrable (outlierTerm H B c) (boxMeasure m (-Real.pi/2)) := by
  exact ((integrable_bounded _ (continuous_insideProduct H Bᶜ).measurable
    (insideProduct_abs_le_one H Bᶜ)).indicator (measurableSet_arcEvent Bᶜ c localRadius)).const_mul _

lemma localTerm_integrable (H : SimpleGraph (Fin (n+1))) (t c : ℝ) :
    Integrable (localTerm H t c) (boxMeasure (n+1) (-Real.pi/2)) := by
  exact (integrable_bounded _ (measurable_badKernel H 0 t) (badKernel_abs_le_one H 0 t)).indicator
    (measurableSet_arcEvent Finset.univ c localRadius)

lemma centerMajorant_integrable (H : SimpleGraph (Fin (n+1))) (t c : ℝ) :
    Integrable (centerMajorant H t c) (boxMeasure (n+1) (-Real.pi/2)) := by
  exact ((integrable_const _).add
    (integrable_finsetSum _ (fun B _ => outlierTerm_integrable H B c))).add (localTerm_integrable H t c)

lemma large_complement (hm : 64 ≤ m) (B : Finset (Fin m))
    (hb : (B.card : ℝ) < (m : ℝ)/4) : 8 ≤ Bᶜ.card := by
  have hm' : (64 : ℝ) ≤ m := by exact_mod_cast hm
  have hcard : (Bᶜ.card : ℝ)+(B.card : ℝ) = m := by
    exact_mod_cast (by simp : Bᶜ.card+B.card=m)
  have hc : (8 : ℝ) ≤ Bᶜ.card := by linarith
  exact_mod_cast hc

lemma outlierTerm_integral_bound (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (hm : 64 ≤ m) (B : Finset (Fin m)) (hB : B ∈ outlierSets m) (c : ℝ) :
    (∫ x, outlierTerm H B c x ∂boxMeasure m (-Real.pi/2)) ≤
      Real.exp (-kappa1*(m : ℝ)*B.card/2) *
        (Real.pi^B.card * (Real.pi*Real.exp 4*Z (m-B.card) 1)) := by
  unfold outlierTerm
  rw [integral_const_mul]
  have h := inside_cluster_integral_bound H hdegree Bᶜ
    (large_complement hm B (Finset.mem_filter.mp hB).2.2) c
  have hb : B.card ≤ m := by simpa using B.card_le_univ
  simp only [Finset.card_compl, Fintype.card_fin, Nat.sub_sub_self hb] at h
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- This is the actual root-fixed tail integral from the proof plan. -/
def tailIntegral (H : SimpleGraph (Fin (n+1))) (t : ℝ) : ℝ :=
  ∫ z, (realBad t).indicator (fun z => kernel H (Fin.cons 0 z)) z ∂boxMeasure n (-Real.pi/2)

def outlierSum (m : ℕ) : ℝ :=
  ∑ B ∈ outlierSets m, Real.pi^B.card * Z (m-B.card) 1 * Real.exp (-kappa1*(m : ℝ)*B.card/2)

/-- Actual finite integral bound, before the finite subset sum is compressed to a
geometric series. No assumed tail estimate enters. -/
theorem tailIntegral_subset_bound (H : SimpleGraph (Fin (n+1)))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 64 ≤ n+1) (t : ℝ) (ht : 0 ≤ t) :
    tailIntegral H t ≤ 16 *
      (Real.pi^n*farConstant (n+1) + Real.exp 4*outlierSum (n+1) +
        2*n*Real.exp 4*Z (n+1) 1*Real.exp (-((n+1 : ℝ)-4)*t^2/4)) := by
  have hi := integrable_bounded (boxMeasure (n+1) (-Real.pi/2))
    (measurable_badKernel H 0 t) (badKernel_abs_le_one H 0 t)
  have hsum := integrable_finsetSum Finset.univ
    (fun j _ => centerMajorant_integrable H t (center j))
  have hp := integral_mono_ae hi hsum (ae_of_all _ (full_pointwise_majorant H hdegree hm t))
  rw [cosine_gauge_real H ht, integral_finsetSum _ (fun j _ => centerMajorant_integrable H t (center j))] at hp
  have hc (c : ℝ) :
      (∫ x, centerMajorant H t c x ∂boxMeasure (n+1) (-Real.pi/2)) ≤
      Real.pi * (Real.pi^n*farConstant (n+1) + Real.exp 4*outlierSum (n+1) +
        2*n*Real.exp 4*Z (n+1) 1*Real.exp (-((n+1 : ℝ)-4)*t^2/4)) := by
    have hconst : Integrable (fun _ : Fin (n+1) → ℝ => farConstant (n+1))
        (boxMeasure (n+1) (-Real.pi/2)) := integrable_const _
    have hout : Integrable (fun x => ∑ B ∈ outlierSets (n+1), outlierTerm H B c x)
        (boxMeasure (n+1) (-Real.pi/2)) :=
      integrable_finsetSum (outlierSets (n+1)) (fun B _ => outlierTerm_integrable H B c)
    have hadd := integral_add (hconst.add hout) (localTerm_integrable H t c)
    simp only [Pi.add_apply] at hadd
    unfold centerMajorant
    rw [hadd,
      integral_add hconst hout,
      integral_finsetSum _ (fun B _ => outlierTerm_integrable H B c)]
    have ho := Finset.sum_le_sum (fun B hB => outlierTerm_integral_bound H hdegree hm B hB c)
    have hl := localContribution_bound H hdegree (by omega) t ht c
    change (∫ x, localTerm H t c x ∂boxMeasure (n+1) (-Real.pi/2)) ≤ _ at hl
    have he : (∑ B ∈ outlierSets (n+1), Real.exp (-kappa1*((n+1 : ℕ) : ℝ)*B.card/2) *
        (Real.pi^B.card*(Real.pi*Real.exp 4*Z (n+1-B.card) 1))) =
        Real.pi * Real.exp 4 * outlierSum (n+1) := by
      rw [outlierSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      ring
    rw [he] at ho
    simp only [integral_const, box_mass, smul_eq_mul]
    rw [pow_succ]
    nlinarith
  have hcenters := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 16))) => hc (center j))
  have htotal := hp.trans hcenters
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at htotal
  change Real.pi * tailIntegral H t ≤ _ at htotal
  nlinarith [Real.pi_pos]

end UniformTorusTail
