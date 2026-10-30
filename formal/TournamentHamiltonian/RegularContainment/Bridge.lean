module

public import TournamentHamiltonian.RegularContainment.Gaussian
public import TournamentHamiltonian.RegularContainment.Scalar
public import TournamentHamiltonian.RegularFourier.Endpoint
public import TournamentHamiltonian.LocalLogCos.Integral

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularContainment
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral PDGaussian RootGaussianTail Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

def torusIntegrand (F : EdgeSet (n+1)) (x : Fin n → ℝ) : ℂ :=
  RegularFourier.signedKernel (RegularFourier.forestEdges F) (RegularFourier.forestOrientation F) (Fin.cons 0 x)

def torusIntegral (F : EdgeSet (n+1)) : ℂ :=
  RegularFourier.rootIntegral (RegularFourier.forestEdges F) (RegularFourier.forestOrientation F)

def quarticConstant : ℝ := Real.exp (-(1:ℝ)/2)

lemma quarticConstant_pos : 0 < quarticConstant := Real.exp_pos _

lemma torusIntegrand_phasedProduct (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    torusIntegrand F x = LocalLogCos.phasedProduct F x := by
  rw [torusIntegrand, RegularFourier.forest_signedKernel, LocalLogCos.phasedProduct,
    LocalLogCos.cosProduct_complex_upper_if, root_phase_identity]
  rfl

lemma torusIntegrand_norm (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    ‖torusIntegrand F x‖ = TorusCluster.kernel (graph F) (Fin.cons 0 x) :=
  RegularFourier.forest_kernel_norm F _

lemma rootCube_eq_pi (r : ℝ) : rootCube n r = univ.pi (fun _ => Icc (-r) r) := by
  ext x
  simp only [mem_pi, mem_univ, forall_true_left, mem_Icc, rootCube, mem_ofPred_eq, abs_le]

lemma boxMeasure_eq_rootCube : PeriodicBox.boxMeasure n (-Real.pi/2) =
    (volume : Measure (Fin n → ℝ)).restrict (rootCube n (Real.pi/2)) := by
  rw [rootCube_eq_pi, PeriodicBox.boxMeasure_eq_closed]
  simp only [neg_div, show -(Real.pi/2)+Real.pi=Real.pi/2 by ring]

lemma torusIntegrand_integrableOn (F : EdgeSet (n+1)) :
    IntegrableOn (torusIntegrand F) (rootCube n (Real.pi/2)) := by
  have h := RegularFourier.root_integrable (RegularFourier.forestEdges F) (RegularFourier.forestOrientation F)
  rwa [boxMeasure_eq_rootCube] at h

lemma torusIntegral_eq (F : EdgeSet (n+1)) :
    torusIntegral F = ∫ x in rootCube n (Real.pi/2), torusIntegrand F x := by
  unfold torusIntegral RegularFourier.rootIntegral
  rw [boxMeasure_eq_rootCube]
  rfl

lemma rootCube_mono {r s : ℝ} (h : r ≤ s) : rootCube n r ⊆ rootCube n s :=
  fun _ hx i => (hx i).trans h

lemma rootCube_compl_eq_bad (r : ℝ) : (rootCube n r)ᶜ = PeriodicBox.realBad r := by
  ext x
  simp [rootCube, PeriodicBox.realBad]

lemma tailIntegral_eq (F : EdgeSet (n+1)) (r : ℝ) :
    UniformTorusTail.tailIntegral (graph F) r =
      ∫ x in rootCube n (Real.pi/2) \ rootCube n r, ‖torusIntegrand F x‖ := by
  unfold UniformTorusTail.tailIntegral
  rw [boxMeasure_eq_rootCube, ← rootCube_compl_eq_bad,
    integral_indicator ((rootCube_measurable n r).compl),
    Measure.restrict_restrict ((rootCube_measurable n r).compl)]
  rw [show (rootCube n r)ᶜ ∩ rootCube n (Real.pi/2) = rootCube n (Real.pi/2) \ rootCube n r by ext; simp; tauto]
  simp only [torusIntegrand_norm]

lemma phase_norm (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    ‖phaseKernel (rootMatrix F) (rootImbalance F) x‖ = realKernel (rootMatrix F) 0 x := by
  simp [phaseKernel, Complex.norm_exp, realKernel]

lemma phase_integral_eq (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) :
    (∫ x, phaseKernel (rootMatrix F) (rootImbalance F) x) = (Z (n+1) 1 * gaussianFactor F : ℝ) := by
  have h := forest_integral_ratio F hm
  have he : (∫ x : Fin n → ℝ, realKernel (rootMatrix (emptyEdgeSet (n+1))) 0 x) = Z (n+1) 1 := by
    rw [completeRoot_empty]
    simp [Z, partition, density]
  rw [he] at h
  have hz : (Z (n+1) 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (partition_pos n 1 (by norm_num)).ne'
  rw [div_eq_iff hz] at h
  simpa [mul_comm] using h

/-- The pure phase is explicitly distinguished from Γ. -/
def purePhase (F : EdgeSet (n+1)) : ℝ :=
  Z (n+1) 1 * gaussianFactor F / normalization (rootMatrix F)

lemma purePhase_lower (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) :
    Real.exp (-5) ≤ purePhase F := by
  have hz : 0 < Z (n+1) 1 := partition_pos n 1 (by norm_num)
  have hA := normalization_pos (rootMatrix_posDef F hm)
  have hn := (normalization_comparison F hm).2
  have hg := (gaussianFactor_bounds F hm).1
  apply (le_div_iff₀ hA).mpr
  calc
    Real.exp (-5)*normalization (rootMatrix F) ≤ Real.exp (-5)*(Real.exp 4*Z (n+1) 1) :=
      mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
    _ = Z (n+1) 1*Real.exp (-1) := by rw [← mul_assoc, ← Real.exp_add]; norm_num; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hg hz.le

lemma purePhase_upper (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) : purePhase F ≤ 1 := by
  have h := norm_integral_le_integral_norm (μ := volume) (phaseKernel (rootMatrix F) (rootImbalance F))
  simp only [phase_norm, zero_integral (rootMatrix_posDef F hm), phase_integral_eq F hm,
    Complex.norm_real, Real.norm_eq_abs] at h
  have hz : 0 < Z (n+1) 1 := partition_pos n 1 (by norm_num)
  rw [abs_of_pos (mul_pos hz (gaussianFactor_uniform_log_error F hm).1)] at h
  exact (div_le_one (normalization_pos (rootMatrix_posDef F hm))).mpr h

end RegularContainment
