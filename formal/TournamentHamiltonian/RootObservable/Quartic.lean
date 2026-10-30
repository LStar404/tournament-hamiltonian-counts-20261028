module

public import TournamentHamiltonian.RootObservable.Transport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootObservable
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral ForestQuartic PDGaussian GaussianQuartic
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

/-- The physical grounded quartic: retained unordered pairs, coefficient exactly 1/12. -/
def rootQuartic (F : EdgeSet (n+1)) (x : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ ¬ (graph F).Adj i j),
    (rootLift x i-rootLift x j)^4)/12

theorem rootQuartic_nonneg (F : EdgeSet (n+1)) (x : Fin n → ℝ) : 0 ≤ rootQuartic F x := by
  unfold rootQuartic
  positivity

theorem rootQuartic_continuous (F : EdgeSet (n+1)) : Continuous (rootQuartic F) := by
  unfold rootQuartic rootLift
  fun_prop

theorem edge4_reconstruct (t : ℝ) (x : Fin n → ℝ) (i j : Fin (n+1)) :
    edge4 i j (reconstruct t x) = (n+1 : ℝ)^2*(rootLift x i-rootLift x j)^4 := by
  have hs : Real.sqrt (n+1 : ℝ)^2 = (n+1 : ℝ) := Real.sq_sqrt (by positivity)
  unfold edge4 reconstruct
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  calc
    _ = (Real.sqrt (n+1 : ℝ)^2)^2*(rootLift x i-rootLift x j)^4 := by ring
    _ = _ := by rw [hs]

theorem forestQuartic_reconstruct (F : EdgeSet (n+1)) (t : ℝ) (x : Fin n → ℝ) :
    forestQuartic F (reconstruct t x) = rootQuartic F x := by
  unfold forestQuartic rootQuartic
  simp_rw [edge4_reconstruct]
  simp only [← Finset.mul_sum]
  push_cast
  have hm : (n+1 : ℝ) ≠ 0 := by positivity
  field_simp

theorem forestQuartic_eq_rootQuartic (F : EdgeSet (n+1)) (y : Fin (n+1) → ℝ) :
    forestQuartic F y = rootQuartic F (rootCoordinates y) := by
  rw [← forestQuartic_reconstruct F (y 0), reconstruct_rootCoordinates]

def rootExpDeviation (F : EdgeSet (n+1)) (x : Fin n → ℝ) : ℝ :=
  |Real.exp (-rootQuartic F x)-Real.exp (-(1/2 : ℝ))|

theorem rootExpDeviation_continuous (F : EdgeSet (n+1)) : Continuous (rootExpDeviation F) := by
  have h := rootQuartic_continuous F
  unfold rootExpDeviation
  fun_prop

theorem rootExpDeviation_nonneg (F : EdgeSet (n+1)) (x : Fin n → ℝ) : 0 ≤ rootExpDeviation F x :=
  abs_nonneg _

theorem rootExpDeviation_le_one (F : EdgeSet (n+1)) (x : Fin n → ℝ) : rootExpDeviation F x ≤ 1 := by
  have h1 : Real.exp (-rootQuartic F x) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rootQuartic_nonneg F x))
  have h2 : Real.exp (-(1/2 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  unfold rootExpDeviation
  rw [abs_le]
  constructor <;> linarith [Real.exp_pos (-rootQuartic F x), Real.exp_pos (-(1/2 : ℝ))]

theorem expDeviation_rootCoordinates (F : EdgeSet (n+1)) (y : Fin (n+1) → ℝ) :
    expDeviation F y = rootExpDeviation F (rootCoordinates y) := by
  rw [ForestQuartic.expDeviation, rootExpDeviation, forestQuartic_eq_rootQuartic]

/-- Actual integrability under grounded ordinary Lebesgue volume. -/
theorem root_expDeviation_integrable (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) :
    Integrable (fun x => realKernel (rootMatrix F) 0 x * rootExpDeviation F x) :=
  kernel_mul_bounded_integrable (rootMatrix_posDef F hm) _
    (rootExpDeviation_continuous F).measurable 1
    (fun x => by simpa only [abs_of_nonneg (rootExpDeviation_nonneg F x)] using rootExpDeviation_le_one F x)

/-- Exact normalized full/root equality for the actual quartic exponential error observable. -/
theorem root_expDeviation_transport (F : EdgeSet (n+1)) (hm : 8 ≤ n+1) :
    (∫ y, kernelDensity F y * expDeviation F y) / normalization (K F) =
      (∫ x, realKernel (rootMatrix F) 0 x * rootExpDeviation F x) / normalization (rootMatrix F) := by
  simp_rw [expDeviation_rootCoordinates]
  exact bounded_observable_integral_ratio F hm _ (rootExpDeviation_continuous F).measurable 1
    (fun x => by simpa only [abs_of_nonneg (rootExpDeviation_nonneg F x)] using rootExpDeviation_le_one F x)

/-- Uniform actual root-kernel L1 quartic exponential error; all Jacobians have been transported. -/
theorem root_expDeviation_bound (F : EdgeSet (n+1)) (hm : 16 ≤ n+1) :
    (∫ x, realKernel (rootMatrix F) 0 x * rootExpDeviation F x) / normalization (rootMatrix F) ≤
      errorRate (n+1) := by
  rw [← root_expDeviation_transport F (by omega)]
  exact volume_expDeviation_bound F hm

theorem root_expDeviation_bound_unnormalized (F : EdgeSet (n+1)) (hm : 16 ≤ n+1) :
    (∫ x, realKernel (rootMatrix F) 0 x * rootExpDeviation F x) ≤
      errorRate (n+1)*normalization (rootMatrix F) :=
  (div_le_iff₀ (normalization_pos (rootMatrix_posDef F (by omega)))).mp
    (root_expDeviation_bound F hm)

/-- The grounded expectation tends to zero uniformly over arbitrary genuine F_m. -/
theorem root_expDeviation_tendsto (F : ∀ n : ℕ, EdgeSet (n+1)) :
    Filter.Tendsto (fun n =>
      (∫ x, realKernel (rootMatrix (F n)) 0 x * rootExpDeviation (F n) x) /
        normalization (rootMatrix (F n))) Filter.atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (errorRate_tendsto.comp (Filter.tendsto_add_atTop_nat 1))
  · filter_upwards [Filter.eventually_ge_atTop 15] with n hn
    apply div_nonneg
    · exact integral_nonneg (fun x => mul_nonneg (Real.exp_nonneg _) (rootExpDeviation_nonneg _ _))
    · exact (normalization_pos (rootMatrix_posDef (F n) (by omega))).le
  · filter_upwards [Filter.eventually_ge_atTop 15] with n hn
    exact root_expDeviation_bound (F n) (by omega)

end RootObservable
