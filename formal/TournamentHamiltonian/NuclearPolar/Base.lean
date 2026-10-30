module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.SingularValues

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NuclearPolar
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual matrix absolute value, including singular and nonnormal matrices. -/
def modulus (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := CFC.abs M

/-- The genuine nuclear norm, not rank times operator norm. -/
def nuclearNorm (M : Matrix ι ι ℂ) : ℝ := (modulus M).trace.re

theorem modulus_eq_sqrt (M : Matrix ι ι ℂ) : modulus M = CFC.sqrt (Mᴴ*M) := rfl

theorem modulus_posSemidef (M : Matrix ι ι ℂ) : (modulus M).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg M)

theorem modulus_sq (M : Matrix ι ι ℂ) : modulus M*modulus M = Mᴴ*M :=
  CFC.abs_mul_abs M

theorem modulus_norm (M : Matrix ι ι ℂ) : ‖modulus M‖ = ‖M‖ := CFC.norm_abs

theorem nuclearNorm_nonneg (M : Matrix ι ι ℂ) : 0 ≤ nuclearNorm M :=
  (RCLike.nonneg_iff.mp (modulus_posSemidef M).trace_nonneg).1

/-- The actual nonnegative spectral values of the matrix absolute value. -/
def spectralValues (M : Matrix ι ι ℂ) : ι → ℝ := (modulus_posSemidef M).isHermitian.eigenvalues

theorem spectralValues_nonneg (M : Matrix ι ι ℂ) (i : ι) : 0 ≤ spectralValues M i :=
  (modulus_posSemidef M).eigenvalues_nonneg i

theorem nuclearNorm_eq_sum_spectralValues (M : Matrix ι ι ℂ) :
    nuclearNorm M = ∑ i, spectralValues M i := by
  rw [nuclearNorm,(modulus_posSemidef M).isHermitian.trace_eq_sum_eigenvalues]
  simp [spectralValues]

theorem trace_modulus (M : Matrix ι ι ℂ) : (modulus M).trace = (nuclearNorm M : ℂ) := by
  rw [nuclearNorm_eq_sum_spectralValues,(modulus_posSemidef M).isHermitian.trace_eq_sum_eigenvalues]
  simp [spectralValues]

/-- Explicitly identifies the trace-square-root definition with the actual Gram singular-value sum. -/
theorem nuclearNorm_eq_sum_sqrt_gram_eigenvalues (M : Matrix ι ι ℂ) :
    nuclearNorm M = ∑ i, Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self M).isHermitian.eigenvalues i) := by
  let hG := Matrix.posSemidef_conjTranspose_mul_self M
  rw [nuclearNorm,modulus_eq_sqrt,CFC.sqrt_eq_cfc,cfc_nnreal_eq_real _ (Mᴴ*M),hG.isHermitian.cfc_eq]
  simp only [Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply,Real.coe_sqrt,Real.coe_toNNReal']
  rw [Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,Matrix.one_mul,Matrix.trace_diagonal]
  simp only [Complex.re_sum,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [max_eq_left (hG.eigenvalues_nonneg i)]
  norm_cast
end NuclearPolar
