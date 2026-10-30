module

public import TournamentHamiltonian.PeriodicBox.Local
public import TournamentHamiltonian.TorusCluster.LocalProduct
public import TournamentHamiltonian.RootGaussianTail.AnchorBad

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace UniformTorusTail
open MeasureTheory Set Function PeriodicBox TorusCluster RootGaussianTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Ordinary closed real cube measure. -/
def cubeMeasure (n : ℕ) (l u : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Icc l u))
instance cubeMeasure_isFiniteMeasure (n : ℕ) (l u : ℝ) : IsFiniteMeasure (cubeMeasure n l u) := by
  unfold cubeMeasure; infer_instance

lemma cubeMeasure_eq (n : ℕ) (l u : ℝ) : cubeMeasure n l u =
    (volume : Measure (Fin n → ℝ)).restrict (univ.pi (fun _ => Icc l u)) := by
  rw [volume_pi, Measure.restrict_pi_pi]; rfl

lemma cube_prod_le_anchor (n : ℕ) (l u : ℝ) :
    (volume.restrict (Icc l u)).prod (cubeMeasure n l u) ≤ anchorMeasure n l u := by
  unfold anchorMeasure
  apply Measure.prod_mono le_rfl
  rw [cubeMeasure_eq]
  exact Measure.restrict_le_self

lemma cube_cons_integral (n : ℕ) (l u : ℝ) (g : (Fin (n+1) → ℝ) → ℝ) :
    (∫ x, g x ∂cubeMeasure (n+1) l u) =
      ∫ y : ℝ × (Fin n → ℝ), g (Fin.cons y.1 y.2)
        ∂(volume.restrict (Icc l u)).prod (cubeMeasure n l u) := by
  have hmp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => volume.restrict (Icc l u)) 0).symm
  simpa only [cubeMeasure, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq]
    using (hmp.integral_comp' g).symm

/-- Actual finite-cube anchor bound for an arbitrary genuine integrable root weight. -/
theorem cube_anchor_bound (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f) (hm : Measurable f) (h0 : ∀ x, 0 ≤ f x) (l u : ℝ) :
    (∫ x : Fin (n+1) → ℝ, f (fun i => x i.succ-x 0) ∂cubeMeasure (n+1) l u) ≤
      max (u-l) 0 * ∫ x, f x := by
  rw [cube_cons_integral]
  simp only [Fin.cons_succ, Fin.cons_zero]
  change (∫ y, anchorWeight n f y ∂(volume.restrict (Icc l u)).prod (cubeMeasure n l u)) ≤ _
  exact (integral_mono_measure (cube_prod_le_anchor n l u)
    (ae_of_all _ (fun y => h0 _)) (anchorWeight_integrable n f hf hm l u)).trans_eq
    (anchorWeight_integral n f hf hm l u)

lemma cube_anchor_integrable (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f) (hm : Measurable f) (l u : ℝ) :
    Integrable (fun x : Fin (n+1) → ℝ => f (fun i => x i.succ-x 0))
      (cubeMeasure (n+1) l u) := by
  have hi := (anchorWeight_integrable n f hf hm l u).mono_measure (cube_prod_le_anchor n l u)
  change Integrable (fun y : ℝ × (Fin n → ℝ) => f (fun i => y.2 i-y.1))
    ((volume.restrict (Icc l u)).prod (cubeMeasure n l u)) at hi
  have hmp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => volume.restrict (Icc l u)) 0).symm
  apply (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mp
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq,
    Fin.cons_succ, Fin.cons_zero, cubeMeasure, anchorWeight] using hi

lemma pairEnergy_eq_completeEnergy (m : ℕ) (x : Fin m → ℝ) :
    pairEnergy m x = completeEnergy x Finset.univ := by
  have h1 := ordered_pair_energy m x
  have h2 := twice_completeEnergy x Finset.univ
  nlinarith

lemma kernel_eq_inside_univ {m : ℕ} (H : SimpleGraph (Fin m)) (x : Fin m → ℝ) :
    kernel H x = insideProduct H x Finset.univ := by
  simp [kernel, insideProduct, insideEdges]

/-- The A and C quadratic forms are exactly identified, with no factor-two loss. -/
lemma kernel_le_pair_gaussian {m : ℕ} (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 0 < m) (x : Fin m → ℝ)
    (hspan : ∀ i j, |x i-x j| ≤ Real.pi/2) :
    kernel H x ≤ Real.exp (-(1-4/(m : ℝ))*pairEnergy m x/2) := by
  rw [kernel_eq_inside_univ]
  have h := inside_gaussian_bound H hdegree x Finset.univ (fun i _ j _ => hspan i j)
  have he : pairEnergy m x = (m : ℝ)*varianceOn x Finset.univ := by
    rw [pairEnergy_eq_completeEnergy, completeEnergy_eq_variance]
    simp
  simp only [Finset.card_univ, Fintype.card_fin] at h
  refine h.trans_eq ?_
  rw [he]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  congr 1
  field_simp

end UniformTorusTail
