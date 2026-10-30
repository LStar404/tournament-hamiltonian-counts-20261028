module

public import TournamentHamiltonian.GaussianSeries
public import Mathlib.Probability.Moments.MGFAnalytic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace PaperGaussianRecovery
open TournamentHamiltonian ProbabilityTheory MeasureTheory Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable
variable {ι : Type*} [Fintype ι]

theorem gaussian_interior (B : Matrix ι ι ℝ) (t : ℝ) (hgap : |t| *‖B‖<1) :
    t ∈ interior (integrableExpSet (gaussianBilinearVariable B) independentStandardGaussian) := by
  have ho : IsOpen {s : ℝ | |s| *‖B‖<1} :=
    isOpen_lt (continuous_abs.mul continuous_const) continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (ho.mem_nhds hgap) (fun s hs => gaussianBilinear_exp_integrable B s hs)

theorem gramGaussian_iteratedDeriv_at (B : Matrix ι ι ℝ) (t : ℝ)
    (hgap : |t| *‖B‖<1) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => gramGaussian (s • B)) t =
      ∫ p, (gaussianBilinearVariable B p)^k * Real.exp (t*gaussianBilinearVariable B p)
        ∂independentStandardGaussian := by
  have ho : IsOpen {s : ℝ | |s| *‖B‖<1} :=
    isOpen_lt (continuous_abs.mul continuous_const) continuous_const
  have he : mgf (gaussianBilinearVariable B) independentStandardGaussian =ᶠ[𝓝 t]
      (fun s : ℝ => gramGaussian (s • B)) := by
    filter_upwards [ho.mem_nhds hgap] with s hs
    exact gaussianBilinear_mgf_eq B s hs
  have h := he.iteratedDeriv_eq k
  rw [iteratedDeriv_mgf (gaussian_interior B t hgap)] at h
  exact h.symm

set_option maxHeartbeats 400000 in
/-- True exponential-series integration with the quadratic multiplier. -/
theorem shifted_second_moment_hasSum (B : Matrix ι ι ℝ) (t : ℝ)
    (hgap : |t| *‖B‖<1) :
    HasSum (fun k : ℕ => gaussianBilinearMoment B (k+2)/(k.factorial:ℝ)*t^k)
      (iteratedDeriv 2 (fun s : ℝ => gramGaussian (s • B)) t) := by
  let X := gaussianBilinearVariable B
  let μ := independentStandardGaussian (ι:=ι) (ρ:=ι)
  have hX : AEStronglyMeasurable X μ := by
    simpa only [pow_one] using (gaussianBilinear_pow_integrable B 1).aestronglyMeasurable
  have hp := integrable_pow_mul_exp_of_mem_interior_integrableExpSet (gaussian_interior B t hgap) 2
  have hn := integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (gaussian_interior B (-t) (by simpa using hgap)) 2
  have hdom : Integrable (fun p => (X p)^2 * Real.exp |t*X p|) μ := by
    apply (hp.add hn).mono'
      ((hX.pow 2).mul (Real.continuous_exp.comp_aestronglyMeasurable (continuous_abs.comp_aestronglyMeasurable (hX.const_mul t))))
    filter_upwards [] with p
    change ‖(X p)^2 * Real.exp |t*X p|‖ ≤ (X p)^2 * Real.exp (t*X p) + (X p)^2 * Real.exp ((-t)*X p)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_pos (Real.exp_pos _)]
    by_cases ht : 0≤t*X p
    · rw [abs_of_nonneg ht]
      exact le_add_of_nonneg_right (by positivity)
    · rw [abs_of_nonpos (le_of_not_ge ht),neg_mul]
      exact le_add_of_nonneg_left (by positivity)
  let F := fun (k : ℕ) (p : (ι → ℝ) × (ι → ℝ)) => (X p)^2*((t*X p)^k/(k.factorial:ℝ))
  let bound := fun (k : ℕ) (p : (ι → ℝ) × (ι → ℝ)) => (X p)^2*(|t*X p|^k/(k.factorial:ℝ))
  have hmeas (k : ℕ) : AEStronglyMeasurable (F k) μ := by
    convert (hX.pow 2).mul (((hX.const_mul t).pow k).mul_const ((k.factorial:ℝ)⁻¹)) using 1
    funext p
    simp only [F,div_eq_mul_inv,Pi.mul_apply,Pi.pow_apply]
  have hbound (k : ℕ) : ∀ᵐ p ∂μ,‖F k p‖≤bound k p := by
    filter_upwards [] with p
    simp [F,bound,Real.norm_eq_abs]
  have hsumbound : ∀ᵐ p ∂μ,Summable (fun k => bound k p) := by
    filter_upwards [] with p
    exact (NormedSpace.expSeries_div_hasSum_exp |t*X p|).summable.mul_left ((X p)^2)
  have hbint : Integrable (fun p => ∑' k,bound k p) μ := by
    have heq : (fun p => ∑' k,bound k p) = (fun p => (X p)^2*Real.exp |t*X p|) := by
      funext p
      dsimp [bound]
      rw [tsum_mul_left,(NormedSpace.expSeries_div_hasSum_exp _).tsum_eq,←Real.exp_eq_exp_ℝ]
    rw [heq]
    exact hdom
  have hlim : ∀ᵐ p ∂μ,HasSum (fun k => F k p) ((X p)^2*Real.exp (t*X p)) := by
    filter_upwards [] with p
    simpa only [F,←Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (t*X p)).mul_left ((X p)^2)
  have hs := hasSum_integral_of_dominated_convergence (μ:=μ) (F:=F)
    (f:=fun p => (X p)^2*Real.exp (t*X p)) bound hmeas hbound hsumbound hbint hlim
  dsimp [F] at hs
  have he (k : ℕ) :
      (∫ p, (X p)^2*((t*X p)^k/(k.factorial:ℝ)) ∂μ) =
        gaussianBilinearMoment B (k+2)/(k.factorial:ℝ)*t^k := by
    have hf : (fun p => (X p)^2*((t*X p)^k/(k.factorial:ℝ))) =
        (fun p => (t^k/(k.factorial:ℝ))*(X p)^(k+2)) := by
      funext p
      simp only [mul_pow,pow_add]
      ring
    rw [hf,integral_const_mul,gaussianBilinearMoment_eq_joint_integral]
    dsimp [X,μ]
    ring
  simp_rw [he] at hs
  rw [gramGaussian_iteratedDeriv_at B t hgap 2]
  exact hs

/-- Actual Gaussian coefficient factorial-second moment, including zero and first coefficients. -/
theorem factorial_second_hasSum (B : Matrix ι ι ℝ) (t : ℝ)
    (hgap : |t| *‖B‖<1) :
    HasSum (fun k : ℕ => (k:ℝ)*((k:ℝ)-1)*bilinearGaussianCoefficient B k*t^k)
      (t^2*iteratedDeriv 2 (fun s : ℝ => gramGaussian (s • B)) t) := by
  let f := fun k : ℕ => (k:ℝ)*((k:ℝ)-1)*bilinearGaussianCoefficient B k*t^k
  have he (k : ℕ) : f (k+2)=t^2*(gaussianBilinearMoment B (k+2)/(k.factorial:ℝ)*t^k) := by
    dsimp [f,bilinearGaussianCoefficient]
    rw [show k+2=(k+1)+1 from rfl,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    rw [pow_add,pow_one]
    field_simp
    ring
  have hs := (shifted_second_moment_hasSum B t hgap).mul_left (t^2)
  change HasSum f _
  apply (hasSum_nat_add_iff' 2).mp
  simp only [show ∑ k ∈ Finset.range 2,f k=0 by simp [f,Finset.sum_range_succ],sub_zero]
  simpa only [he] using hs

end
end PaperGaussianRecovery
