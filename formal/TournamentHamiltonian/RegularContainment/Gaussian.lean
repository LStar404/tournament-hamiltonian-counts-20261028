module

public import TournamentHamiltonian.RegularContainment.Quadratic
public import TournamentHamiltonian.RootGaussianTail.Normalization
public import TournamentHamiltonian.UniformTorusTail.Endpoint

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularContainment
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral PDGaussian RootGaussianTail Set Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

def rootCube (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {x | ∀ i, |x i| ≤ r}

lemma rootCube_measurable (n : ℕ) (r : ℝ) : MeasurableSet (rootCube n r) := by
  have he : rootCube n r = ⋂ i : Fin n, {x | |x i|≤r} := by ext x; simp [rootCube]
  rw [he]
  exact MeasurableSet.iInter (fun i => (isClosed_le (continuous_apply i).abs continuous_const).measurableSet)

lemma realKernel_nonneg (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    0 ≤ realKernel (rootMatrix F) 0 x := (Real.exp_pos _).le

/-- Actual normalizers, established by pointwise whole-space comparison. -/
theorem normalization_comparison (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) :
    Z (n+1) 1 ≤ normalization (rootMatrix F) ∧
    normalization (rootMatrix F) ≤ Real.exp 4 * Z (n+1) 1 := by
  have hi := realKernel_integrable (rootMatrix_posDef F hm) 0
  have ha := perturbation_scale_pos (n+1) hm
  have hl := integral_mono (density_integrable n 1 (by norm_num)) hi
    (fun x => (density_comparison F x).1)
  have hu := integral_mono hi (density_integrable n _ ha)
    (fun x => (density_comparison F x).2)
  rw [zero_integral (rootMatrix_posDef F hm)] at hl hu
  refine ⟨hl, hu.trans ?_⟩
  exact perturbation_normalization_loss (n+1) hm

lemma rootCube_compl_subset (r : ℝ) : (rootCube n r)ᶜ ⊆ maxTail n r := by
  intro x hx
  simp only [mem_compl_iff, rootCube, mem_ofPred_eq, not_forall, not_le] at hx
  obtain ⟨i,hi⟩ := hx
  exact ⟨i,hi.le⟩

def gaussianTailBudget (m : ℕ) (r : ℝ) : ℝ :=
  2*(m-1 : ℕ)*Real.exp 4*Real.exp (-((m:ℝ)-4)*r^2/4)

lemma gaussianTailBudget_nonneg (m : ℕ) (r : ℝ) : 0 ≤ gaussianTailBudget m r := by
  unfold gaussianTailBudget; positivity

/-- The missing full-space Gaussian tail: no local cosine hypothesis is used. -/
theorem gaussian_tail_bound (F : EdgeSet (n+1)) (hm : 8 ≤ n+1)
    (r : ℝ) (hr : 0 ≤ r) :
    (∫ x in (rootCube n r)ᶜ, realKernel (rootMatrix F) 0 x) ≤
      gaussianTailBudget (n+1) r * Z (n+1) 1 := by
  let a : ℝ := 1-4/((n+1:ℕ):ℝ)
  have ha : 0 < a := perturbation_scale_pos (n+1) hm
  have hi := realKernel_integrable (rootMatrix_posDef F hm) 0
  have hd := density_integrable n a ha
  have hcmp := integral_mono (μ := volume.restrict (rootCube n r)ᶜ) hi.integrableOn hd.integrableOn
    (fun x => (density_comparison F x).2)
  have hsub : (∫ x in (rootCube n r)ᶜ, density n a x) ≤ ∫ x in maxTail n r, density n a x := by
    apply integral_mono_measure (Measure.restrict_mono (rootCube_compl_subset r) le_rfl)
      (ae_of_all _ (density_nonneg n a)) hd.integrableOn
  have ht := finite_max_tail n a ha r hr
  have hz := perturbation_normalization_loss (n+1) hm
  simp only [Z, Nat.add_sub_cancel] at hz
  have he : -a*(n+1:ℝ)*r^2/4 = -((n+1:ℝ)-4)*r^2/4 := by
    dsimp [a]
    push_cast
    field_simp
  rw [he] at ht
  refine (hcmp.trans hsub |>.trans ht).trans ?_
  have hn : 0 ≤ 2*(n:ℝ)*Real.exp (-((n+1:ℝ)-4)*r^2/4) := by positivity
  have hp := mul_le_mul_of_nonneg_left hz hn
  simp only [gaussianTailBudget, Z, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  convert hp using 1 <;> ring

lemma gaussianTailBudget_eq_localEnvelope (m : ℕ) (r : ℝ) :
    gaussianTailBudget m r = UniformTorusTail.localEnvelope m r / 16 := by
  unfold gaussianTailBudget UniformTorusTail.localEnvelope
  ring

lemma gaussianTailBudget_tendsto :
    Tendsto (fun m => gaussianTailBudget m (UniformTorusTail.window m (1/16))) atTop (𝓝 0) := by
  simp_rw [gaussianTailBudget_eq_localEnvelope]
  simpa only [zero_div] using
    (UniformTorusTail.tendsto_localEnvelope_window_zero (1/16) (by norm_num)).div_const 16

end RegularContainment
