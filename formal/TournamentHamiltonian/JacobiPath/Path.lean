module

public import TournamentHamiltonian.JacobiPath.Differential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace JacobiPath
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Jacobi for an arbitrary differentiable path, not just a linear polynomial path. -/
theorem hasDerivAt_det_path {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {M : 𝕜 → Matrix n n 𝕜} {H : Matrix n n 𝕜} {t : 𝕜}
    (hM : HasDerivAt M H t) (hdet : (M t).det≠0) :
    HasDerivAt (fun s => (M s).det) ((M t).det*Matrix.trace ((M t)⁻¹*H)) t := by
  have h := (hasFDerivAt_det (M t)).comp_hasDerivAt (f := M) (f' := H) t hM
  convert h using 1
  · rfl
  · exact (detDifferential_apply (M t) H hdet).symm

/-- Real-parameter complex paths need only real differentiability, not holomorphy. -/
theorem hasDerivAt_det_complex_path {M : ℝ → Matrix n n ℂ} {H : Matrix n n ℂ} {t : ℝ}
    (hM : HasDerivAt M H t) (hdet : (M t).det≠0) :
    HasDerivAt (fun s => (M s).det) ((M t).det*Matrix.trace ((M t)⁻¹*H)) t := by
  have h := ((hasFDerivAt_det (M t)).restrictScalars ℝ).comp_hasDerivAt (f := M) (f' := H) t hM
  convert h using 1
  · rfl
  · exact (detDifferential_apply (M t) H hdet).symm

/-- The manuscript's positive-determinant real logarithm, with its guard retained. -/
theorem hasDerivAt_logdet {M : ℝ → Matrix n n ℝ} {H : Matrix n n ℝ} {t : ℝ}
    (hM : HasDerivAt M H t) (hdet : 0<(M t).det) :
    HasDerivAt (fun s => Real.log ((M s).det)) (Matrix.trace ((M t)⁻¹*H)) t := by
  have h := (hasDerivAt_det_path hM hdet.ne').log hdet.ne'
  convert h using 1
  field_simp

theorem deriv_det_path {M : ℝ → Matrix n n ℝ} {t : ℝ}
    (hM : DifferentiableAt ℝ M t) (hdet : (M t).det≠0) :
    deriv (fun s => (M s).det) t = (M t).det*Matrix.trace ((M t)⁻¹*deriv M t) :=
  (hasDerivAt_det_path (DifferentiableAt.hasDerivAt (f := M) hM) hdet).deriv

theorem deriv_det_complex_path {M : ℝ → Matrix n n ℂ} {t : ℝ}
    (hM : DifferentiableAt ℝ M t) (hdet : (M t).det≠0) :
    deriv (fun s => (M s).det) t = (M t).det*Matrix.trace ((M t)⁻¹*deriv M t) :=
  (hasDerivAt_det_complex_path (DifferentiableAt.hasDerivAt (f := M) hM) hdet).deriv

theorem deriv_logdet {M : ℝ → Matrix n n ℝ} {t : ℝ}
    (hM : DifferentiableAt ℝ M t) (hdet : 0<(M t).det) :
    deriv (fun s => Real.log ((M s).det)) t = Matrix.trace ((M t)⁻¹*deriv M t) :=
  (hasDerivAt_logdet (DifferentiableAt.hasDerivAt (f := M) hM) hdet).deriv

end JacobiPath
