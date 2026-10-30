module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace JacobiPath
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
attribute [local instance] Classical.propDecidable Classical.decEq
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual determinant, bundled as continuous multilinear in its rows. -/
def detMultilinear (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (n : Type*) [Fintype n] [DecidableEq n] :
    ContinuousMultilinearMap 𝕜 (fun _ : n => n → 𝕜) 𝕜 where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

@[simp] lemma detMultilinear_apply (A : Matrix n n 𝕜) : detMultilinear 𝕜 n A=A.det := rfl

def detDifferential (A : Matrix n n 𝕜) : Matrix n n 𝕜 →L[𝕜] 𝕜 :=
  (detMultilinear 𝕜 n).linearDeriv A

/-- General Fréchet derivative, valid even at singular matrices. -/
theorem hasFDerivAt_det (A : Matrix n n 𝕜) :
    HasFDerivAt Matrix.det (detDifferential A) A :=
  (detMultilinear 𝕜 n).hasFDerivAt A

lemma detDifferential_rows (A H : Matrix n n 𝕜) :
    detDifferential A H = ∑ i, (A.updateRow i (H i)).det := by
  exact (detMultilinear 𝕜 n).linearDeriv_apply A H

/-- Cramer's rule fixes the row/column and multiplication-order convention. -/
lemma row_replacement (A H : Matrix n n 𝕜) (hA : A.det≠0) (i : n) :
    (A.updateRow i (H i)).det=A.det*(H*A⁻¹) i i := by
  have h := congrFun (Matrix.det_smul_inv_vecMul_eq_cramer_transpose A (H i)
    (isUnit_iff_ne_zero.mpr hA)) i
  rw [Matrix.cramer_transpose_apply] at h
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, Matrix.mul_apply, dotProduct] using h.symm

/-- The determinant Fréchet differential at an invertible point, on every direction. -/
theorem detDifferential_apply (A H : Matrix n n 𝕜) (hA : A.det≠0) :
    detDifferential A H = A.det*Matrix.trace (A⁻¹*H) := by
  rw [detDifferential_rows]
  simp_rw [row_replacement A H hA]
  rw [← Finset.mul_sum]
  change A.det*Matrix.trace (H*A⁻¹)=_
  rw [Matrix.trace_mul_comm]

end JacobiPath
