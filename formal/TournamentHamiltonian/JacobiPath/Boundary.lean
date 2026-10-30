module

public import TournamentHamiltonian.JacobiPath.Path
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace JacobiPath
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
attribute [local instance] Classical.propDecidable Classical.decEq

lemma empty_differential (A H : Matrix (Fin 0) (Fin 0) ℝ) : detDifferential A H=0 := by
  simp [detDifferential_rows]

lemma empty_path (M : ℝ → Matrix (Fin 0) (Fin 0) ℂ) (t : ℝ) :
    HasDerivAt (fun s => (M s).det) 0 t := by
  simpa using hasDerivAt_const t (1:ℂ)

lemma identity_differential {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℝ) :
    detDifferential (1:Matrix n n ℝ) H=Matrix.trace H := by
  rw [detDifferential_apply _ _ (by simp)]
  simp

def baseTwo : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;0,1]
def directionTwo : Matrix (Fin 2) (Fin 2) ℝ := !![0,0;1,0]
def nonlinearPath (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := baseTwo+t•directionTwo+t^2•1

lemma baseTwo_det : baseTwo.det=1 := by norm_num [baseTwo,Matrix.det_fin_two]
lemma baseTwo_inverse : baseTwo⁻¹=!![1,-1;0,1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [baseTwo,Matrix.mul_fin_two]
lemma base_direction_noncommute : baseTwo*directionTwo≠directionTwo*baseTwo := by
  intro h
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
  norm_num [baseTwo,directionTwo,Matrix.mul_fin_two] at hh
lemma nonlinear_derivative : HasDerivAt nonlinearPath directionTwo 0 := by
  have h := ((hasDerivAt_const 0 baseTwo).add ((hasDerivAt_id 0).smul_const directionTwo)).add
    ((hasDerivAt_pow 2 (0:ℝ)).smul_const (1:Matrix (Fin 2) (Fin 2) ℝ))
  convert h using 1 <;> first | rfl | norm_num [nonlinearPath]
lemma nonlinear_value : nonlinearPath 0=baseTwo := by simp [nonlinearPath]
lemma nonlinear_not_affine : nonlinearPath 1+nonlinearPath (-1)≠2•nonlinearPath 0 := by
  intro h
  have hh := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
  norm_num [nonlinearPath,baseTwo,directionTwo] at hh

lemma nonlinear_det_derivative : HasDerivAt (fun t => (nonlinearPath t).det) (-1) 0 := by
  have h := hasDerivAt_det_path nonlinear_derivative (by rw [nonlinear_value,baseTwo_det]; norm_num)
  rw [nonlinear_value,baseTwo_det,baseTwo_inverse] at h
  norm_num [directionTwo,Matrix.mul_fin_two,Matrix.trace,Fin.sum_univ_two] at h ⊢
  exact h

lemma nonlinear_logdet_derivative : HasDerivAt (fun t => Real.log ((nonlinearPath t).det)) (-1) 0 := by
  have h := hasDerivAt_logdet nonlinear_derivative (by rw [nonlinear_value,baseTwo_det]; norm_num)
  rw [nonlinear_value,baseTwo_inverse] at h
  norm_num [directionTwo,Matrix.mul_fin_two,Matrix.trace,Fin.sum_univ_two] at h ⊢
  exact h

lemma negative_det_guard : ¬0<(!![-1]:Matrix (Fin 1) (Fin 1) ℝ).det := by norm_num
lemma singular_guard : (0:Matrix (Fin 1) (Fin 1) ℝ).det=0 := by simp

lemma singular_differential_nonzero :
    detDifferential (!![0,0;0,1]:Matrix (Fin 2) (Fin 2) ℝ) (!![1,0;0,0])=1 := by
  rw [detDifferential_rows]
  norm_num [Fin.sum_univ_two,Matrix.det_fin_two,Matrix.updateRow]

lemma inverse_formula_needs_guard :
    detDifferential (!![0,0;0,1]:Matrix (Fin 2) (Fin 2) ℝ) (!![1,0;0,0]) ≠
      (!![0,0;0,1]:Matrix (Fin 2) (Fin 2) ℝ).det*
        Matrix.trace ((!![0,0;0,1]:Matrix (Fin 2) (Fin 2) ℝ)⁻¹*!![1,0;0,0]) := by
  rw [singular_differential_nonzero]
  norm_num [Matrix.det_fin_two]

/-- A genuine real-parameter complex-valued path. No complex logarithm is asserted. -/
def complexPath (t : ℝ) : Matrix (Fin 1) (Fin 1) ℂ := !![1+(t:ℂ)*Complex.I]

lemma complex_path_derivative : HasDerivAt complexPath (!![Complex.I]) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i
  fin_cases j
  have h := (((hasDerivAt_id (0:ℝ)).ofReal_comp).mul_const Complex.I).const_add 1
  simpa [complexPath] using h

lemma complex_det_derivative : HasDerivAt (fun t => (complexPath t).det) Complex.I 0 := by
  have h := hasDerivAt_det_complex_path complex_path_derivative (by norm_num [complexPath])
  have he : complexPath 0=(1:Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [complexPath]
  rw [he] at h
  norm_num [Matrix.trace,Fin.sum_univ_one] at h ⊢
  exact h

end JacobiPath
