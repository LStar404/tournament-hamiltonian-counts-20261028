module

public import TournamentHamiltonian.PDGaussian.Integral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PDGaussian
open Matrix MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

def realKernel (A : Matrix ι ι ℝ) (b : ι → ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (-(x ⬝ᵥ A *ᵥ x) / 2 + b ⬝ᵥ x)

def phaseKernel (A : Matrix ι ι ℝ) (b : ι → ℝ) (x : ι → ℝ) : ℂ :=
  Complex.exp (-(↑(x ⬝ᵥ A *ᵥ x) : ℂ) / 2 + Complex.I * (b ⬝ᵥ x : ℝ))

theorem bilinear_ofReal (A : Matrix ι ι ℝ) (b : ι → ℝ) :
    bilinear A (fun i => (b i : ℂ)) = (b ⬝ᵥ A *ᵥ b : ℝ) := by
  simp [bilinear, complexify, Matrix.mulVec, dotProduct]

theorem bilinear_smul (A : Matrix ι ι ℝ) (z : ι → ℂ) (c : ℂ) :
    bilinear A (c • z) = c^2 * bilinear A z := by
  simp only [bilinear, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem bilinear_phase (A : Matrix ι ι ℝ) (b : ι → ℝ) :
    bilinear A (fun i => Complex.I * (b i : ℂ)) = -(↑(b ⬝ᵥ A *ᵥ b) : ℂ) := by
  change bilinear A (Complex.I • (fun i => (b i : ℂ))) = _
  rw [bilinear_smul, bilinear_ofReal, Complex.I_sq, neg_one_mul]

theorem kernel_real (A : Matrix ι ι ℝ) (b : ι → ℝ) (x : ι → ℝ) :
    kernel A (fun i => (b i : ℂ)) x = (realKernel A b x : ℂ) := by
  rw [kernel, realKernel, Complex.ofReal_exp]
  congr 1
  simp [dotProduct]

theorem kernel_phase (A : Matrix ι ι ℝ) (b : ι → ℝ) (x : ι → ℝ) :
    kernel A (fun i => Complex.I * (b i : ℂ)) x = phaseKernel A b x := by
  simp only [kernel, phaseKernel, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.mul_sum, mul_assoc]

theorem realKernel_integrable {A : Matrix ι ι ℝ} (hA : A.PosDef) (b : ι → ℝ) :
    Integrable (realKernel A b) := by
  have h := (kernel_integrable hA (fun i => (b i : ℂ))).re
  change Integrable (fun x => (kernel A (fun i => (b i : ℂ)) x).re) at h
  simpa only [kernel_real, Complex.ofReal_re] using h

theorem realKernel_integral {A : Matrix ι ι ℝ} (hA : A.PosDef) (b : ι → ℝ) :
    (∫ x : ι → ℝ, realKernel A b x) =
      normalization A * Real.exp ((b ⬝ᵥ A⁻¹ *ᵥ b) / 2) := by
  apply Complex.ofReal_injective
  have h := kernel_integral hA (fun i => (b i : ℂ))
  simpa only [kernel_real, integral_complex_ofReal, bilinear_ofReal,
    Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_ofNat] using h

theorem phaseKernel_integrable {A : Matrix ι ι ℝ} (hA : A.PosDef) (b : ι → ℝ) :
    Integrable (phaseKernel A b) := by
  have h := kernel_integrable hA (fun i => Complex.I * (b i : ℂ))
  have he : (kernel A (fun i => Complex.I * (b i : ℂ))) = phaseKernel A b :=
    funext (kernel_phase A b)
  rwa [he] at h

theorem phaseKernel_integral {A : Matrix ι ι ℝ} (hA : A.PosDef) (b : ι → ℝ) :
    (∫ x : ι → ℝ, phaseKernel A b x) =
      (normalization A * Real.exp (-(b ⬝ᵥ A⁻¹ *ᵥ b) / 2) : ℝ) := by
  have h := kernel_integral hA (fun i => Complex.I * (b i : ℂ))
  simpa only [kernel_phase, bilinear_phase, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using h

theorem zero_integral {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (∫ x : ι → ℝ, realKernel A 0 x) = normalization A := by
  rw [realKernel_integral hA]
  simp

theorem normalized_MGF {A : Matrix ι ι ℝ} (hA : A.PosDef) (b : ι → ℝ) :
    (∫ x : ι → ℝ, realKernel A b x) / (∫ x : ι → ℝ, realKernel A 0 x) =
      Real.exp ((b ⬝ᵥ A⁻¹ *ᵥ b) / 2) := by
  rw [realKernel_integral hA, zero_integral hA]
  exact mul_div_cancel_left₀ _ (ne_of_gt (normalization_pos hA))

theorem normalized_phase {A : Matrix ι ι ℝ} (hA : A.PosDef) (b : ι → ℝ) :
    (∫ x : ι → ℝ, phaseKernel A b x) / (∫ x : ι → ℝ, realKernel A 0 x : ℝ) =
      (Real.exp (-(b ⬝ᵥ A⁻¹ *ᵥ b) / 2) : ℂ) := by
  rw [phaseKernel_integral hA, zero_integral hA, Complex.ofReal_mul]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (normalization_pos hA)))

theorem single_quadratic (A : Matrix ι ι ℝ) (i : ι) (t : ℝ) :
    Pi.single i t ⬝ᵥ A *ᵥ Pi.single i t = t^2 * A i i := by
  simp only [dotProduct, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Matrix.mulVec, mul_ite, mul_zero]
  ring

theorem coordinate_MGF {A : Matrix ι ι ℝ} (hA : A.PosDef) (i : ι) (t : ℝ) :
    (∫ x : ι → ℝ, Real.exp (-(x ⬝ᵥ A *ᵥ x) / 2 + t * x i)) /
      (∫ x : ι → ℝ, realKernel A 0 x) = Real.exp (t^2 * A⁻¹ i i / 2) := by
  have h := normalized_MGF hA (Pi.single i t)
  rw [single_quadratic] at h
  simpa only [realKernel, single_dotProduct] using h
end PDGaussian
