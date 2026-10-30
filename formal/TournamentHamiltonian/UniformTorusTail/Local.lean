module

public import TournamentHamiltonian.UniformTorusTail.Integration

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace UniformTorusTail
open MeasureTheory Set Function PeriodicBox TorusCluster RootGaussianTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ}

def localRadius : ℝ := 3*Real.pi/16

def localContribution (H : SimpleGraph (Fin (n+1))) (t c : ℝ) : ℝ :=
  ∫ x, (arcEvent Finset.univ c localRadius).indicator (badKernel H 0 t) x
    ∂boxMeasure (n+1) (-Real.pi/2)

lemma measurableSet_differenceBad (root : Fin (n+1)) (t : ℝ) :
    MeasurableSet (differenceBad root t) := by
  unfold differenceBad
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_lt measurable_const
    (((continuous_apply i).sub (continuous_apply root) :
      Continuous (fun x : Fin (n+1) → ℝ => x i-x root)).abs.measurable)

lemma difference_bad_to_maxTail {t : ℝ} (ht : 0 ≤ t) (x : Fin (n+1) → ℝ)
    (hx : x ∈ differenceBad 0 t) : (fun i : Fin n => x i.succ-x 0) ∈ maxTail n t := by
  change ∃ i, t < |x i-x 0| at hx
  rcases Fin.exists_fin_succ.mp hx with h | ⟨i,hi⟩
  · simp at h
    exact (not_lt_of_ge ht h).elim
  · exact ⟨i,hi.le⟩

lemma kernel_le_shifted_density (H : SimpleGraph (Fin (n+1)))
    (hdegree : ∀ i, H.degree i ≤ 2) (x : Fin (n+1) → ℝ)
    (hspan : ∀ i j, |x i-x j| ≤ Real.pi/2) :
    kernel H x ≤ density n (1-4/((n+1 : ℕ) : ℝ)) (fun i => x i.succ-x 0) := by
  have hg := kernel_le_pair_gaussian H hdegree (Nat.succ_pos _) x hspan
  have he := anchorDensity_pair_energy n (1-4/((n+1 : ℕ) : ℝ)) (x 0) (Fin.tail x)
  simp only [anchorDensity, Fin.tail, Fin.cons_self_tail] at he
  rwa [he]

/-- A genuine all-local torus integral is dominated by the genuine root Gaussian
max-tail integral, including the ordinary-volume anchor factor. -/
theorem localContribution_gaussian_bound (H : SimpleGraph (Fin (n+1)))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 8 ≤ n+1) (t : ℝ) (ht : 0 ≤ t) (c : ℝ) :
    localContribution H t c ≤ Real.pi *
      (2*n*partition n (1-4/((n+1 : ℕ) : ℝ))*
        Real.exp (-(1-4/((n+1 : ℕ) : ℝ))*(n+1 : ℝ)*t^2/4)) := by
  let a : ℝ := 1-4/((n+1 : ℕ) : ℝ)
  have ha : 0 < a := perturbation_scale_pos (n+1) hm
  let f : (Fin n → ℝ) → ℝ := (maxTail n t).indicator (density n a)
  have hfi : Integrable f := (density_integrable n a ha).indicator (maxTail_measurable n t)
  have hfm : Measurable f := (density_measurable n a).indicator (maxTail_measurable n t)
  have hf0 (x : Fin n → ℝ) : 0 ≤ f x :=
    Set.indicator_nonneg (fun x _ => density_nonneg n a x) x
  have hgi := cube_anchor_integrable n f hfi hfm (-localRadius) localRadius
  have hsm : Measurable ((differenceBad 0 t).indicator (kernel H)) :=
    (continuous_kernel H).measurable.indicator (measurableSet_differenceBad 0 t)
  have hsb (x : Fin (n+1) → ℝ) : |(differenceBad 0 t).indicator (kernel H) x| ≤ 1 := by
    by_cases hx : x ∈ differenceBad 0 t
    · simpa [hx] using kernel_abs_le_one H x
    · simp [hx]
  have hsi := integrable_bounded (cubeMeasure (n+1) (-localRadius) localRadius) hsm hsb
  have hpoint : ∀ᵐ x ∂cubeMeasure (n+1) (-localRadius) localRadius,
      (differenceBad 0 t).indicator (kernel H) x ≤ f (fun i => x i.succ-x 0) := by
    rw [cubeMeasure_eq]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi (fun _ => measurableSet_Icc))] with x hx
    have hspan (i j : Fin (n+1)) : |x i-x j| ≤ Real.pi/2 := by
      have hi : |x i| ≤ localRadius := abs_le.mpr (hx i (mem_univ i))
      have hj : |x j| ≤ localRadius := abs_le.mpr (hx j (mem_univ j))
      have hab := abs_sub (x i) (x j)
      dsimp [localRadius] at hi hj
      linarith [Real.pi_pos]
    by_cases hb : x ∈ differenceBad 0 t
    · rw [Set.indicator_of_mem hb]
      have hm := difference_bad_to_maxTail ht x hb
      simpa only [f, Set.indicator_of_mem hm] using kernel_le_shifted_density H hdegree x hspan
    · rw [Set.indicator_of_notMem hb]
      exact hf0 _
  have hcmp := integral_mono_ae hsi hgi hpoint
  have hanc := cube_anchor_bound n f hfi hfm hf0 (-localRadius) localRadius
  have htail := finite_max_tail n a ha t ht
  rw [← integral_indicator (maxTail_measurable n t)] at htail
  change (∫ x, f x) ≤ _ at htail
  have hlen : 0 ≤ max (localRadius-(-localRadius)) 0 ∧
      max (localRadius-(-localRadius)) 0 ≤ Real.pi := by
    constructor
    · exact le_max_right _ _
    · apply max_le
      · dsimp [localRadius]; linarith [Real.pi_pos]
      · exact Real.pi_pos.le
  have hnon : 0 ≤ 2*(n : ℝ)*partition n a*Real.exp (-a*(n+1 : ℝ)*t^2/4) := by
    exact mul_nonneg (mul_nonneg (by positivity) (partition_pos n a ha).le) (Real.exp_pos _).le
  unfold localContribution
  rw [unwrap_local_badKernel H 0 t c (by dsimp [localRadius]; linarith [Real.pi_pos])]
  change (∫ x, (differenceBad 0 t).indicator (kernel H) x
    ∂(volume : Measure (Fin (n+1) → ℝ)).restrict (univ.pi (fun _ => Icc (-localRadius) localRadius))) ≤ _
  rw [← cubeMeasure_eq]
  exact (hcmp.trans hanc).trans
    ((mul_le_mul_of_nonneg_left htail hlen.1).trans
      (mul_le_mul_of_nonneg_right hlen.2 hnon))

/-- Exact planned one-center local estimate; normalization is C's actual Gaussian integral. -/
theorem localContribution_bound (H : SimpleGraph (Fin (n+1)))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 8 ≤ n+1) (t : ℝ) (ht : 0 ≤ t) (c : ℝ) :
    localContribution H t c ≤
      Real.pi * (2*n*Real.exp 4*Z (n+1) 1*Real.exp (-((n+1 : ℝ)-4)*t^2/4)) := by
  have h := localContribution_gaussian_bound H hdegree hm t ht c
  have hz := perturbation_normalization_loss (n+1) hm
  simp only [Z, Nat.add_sub_cancel] at hz
  have he : (1-4/((n+1 : ℕ) : ℝ))*(n+1 : ℝ) = (n+1 : ℝ)-4 := by
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
  have hfac : -(1-4/((n+1 : ℕ) : ℝ))*(n+1 : ℝ)*t^2/4 = -((n+1 : ℝ)-4)*t^2/4 := by
    rw [neg_mul, he]
  rw [hfac] at h
  apply h.trans
  have hn : 0 ≤ Real.pi * (2*(n : ℝ)*Real.exp (-((n+1 : ℝ)-4)*t^2/4)) := by positivity
  have hp := mul_le_mul_of_nonneg_left hz hn
  simp only [Z, Nat.add_sub_cancel]
  convert hp using 1 <;> ring

end UniformTorusTail
