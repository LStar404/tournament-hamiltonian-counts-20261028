module

public import TournamentHamiltonian.FrobeniusCp.Estimate

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FrobeniusCp
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
attribute [local instance] Classical.propDecidable Classical.decEq

lemma constant_zero : remainderConstant 0 = 0 := by norm_num [remainderConstant, Finset.sum_filter, Finset.sum_range_succ]
lemma constant_one : remainderConstant 1 = 0 := by norm_num [remainderConstant, Finset.sum_filter, Finset.sum_range_succ]
lemma constant_two : remainderConstant 2 = 2 := by norm_num [remainderConstant, Finset.sum_filter, Finset.sum_range_succ]
lemma constant_three : remainderConstant 3 = 12 := by norm_num [remainderConstant, Finset.sum_filter, Finset.sum_range_succ]
lemma constant_four : remainderConstant 4 = 60 := by norm_num [remainderConstant, Finset.sum_filter, Finset.sum_range_succ, Nat.choose]

lemma empty_remainder (K : Matrix (Fin 0) (Fin 0) ℂ) :
    (1 + K).det - 1 - Matrix.trace K = 0 := by simp [Matrix.trace]

lemma empty_frobenius (K : Matrix (Fin 0) (Fin 0) ℂ) : frobenius K = 0 := by
  simp [frobenius]

lemma one_remainder (K : Matrix (Fin 1) (Fin 1) ℂ) :
    (1 + K).det - 1 - Matrix.trace K = 0 := by
  simp [Matrix.trace, Matrix.diag]

lemma one_nonreal_endpoint : ‖(1 + (!![Complex.I] : Matrix (Fin 1) (Fin 1) ℂ)).det -
    1 - Matrix.trace !![Complex.I]‖ = 0 := by rw [one_remainder, norm_zero]

def singularBoundary : Matrix (Fin 2) (Fin 2) ℝ := !![-1,0;0,0]

lemma singular_boundary_frobenius : frobenius singularBoundary = 1 := by
  norm_num [frobenius, singularBoundary, Fin.sum_univ_succ]

lemma identity_plus_singular : (1 + singularBoundary).det = 0 := by
  norm_num [singularBoundary, Matrix.det_fin_two]

lemma singular_boundary_estimate :
    ‖(1 + singularBoundary).det - 1 - Matrix.trace singularBoundary‖ ≤
      remainderConstant 2 * frobenius singularBoundary ^ 2 := by
  exact determinant_remainder_bound singularBoundary (by rw [singular_boundary_frobenius])

def nonnormalComplex : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I/2,1/2;0,Complex.I/2]

lemma nonnormal_complex :
    nonnormalComplex * nonnormalComplex.conjTranspose ≠
      nonnormalComplex.conjTranspose * nonnormalComplex := by
  intro h
  have e := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => (A 0 0).re) h
  norm_num [nonnormalComplex, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ] at e
  linarith

lemma nonnormal_frobenius_sq : frobenius nonnormalComplex ^ 2 = 3/4 := by
  rw [frobenius_sq]
  norm_num [nonnormalComplex, Fin.sum_univ_succ, norm_div]

lemma nonnormal_remainder :
    (1 + nonnormalComplex).det - 1 - Matrix.trace nonnormalComplex = -(1/4 : ℂ) := by
  norm_num [nonnormalComplex, Matrix.det_fin_two, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  ring_nf
  simp
  ring

lemma nonnormal_estimate :
    ‖(1 + nonnormalComplex).det - 1 - Matrix.trace nonnormalComplex‖ ≤
      remainderConstant 2 * frobenius nonnormalComplex ^ 2 := by
  apply determinant_remainder_bound
  apply (sq_le_sq₀ (frobenius_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
  rw [nonnormal_frobenius_sq]
  norm_num

def largeDiagonal : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal (fun _ => 100)

lemma large_remainder :
    (1 + largeDiagonal).det - 1 - Matrix.trace largeDiagonal = 1030000 := by
  have h : 1 + largeDiagonal = Matrix.diagonal (fun _ : Fin 3 => (101:ℝ)) := by
    ext i j
    by_cases hij : i=j <;> norm_num [largeDiagonal, hij]
  rw [h, Matrix.det_diagonal]
  norm_num [largeDiagonal, Matrix.trace_diagonal]

lemma large_frobenius_sq : frobenius largeDiagonal ^ 2 = 30000 := by
  rw [frobenius_sq]
  norm_num [largeDiagonal, Matrix.diagonal_apply, Fin.sum_univ_succ]

lemma smallness_guard_needed : ¬ (‖(1 + largeDiagonal).det - 1 - Matrix.trace largeDiagonal‖ ≤
    remainderConstant 3 * frobenius largeDiagonal ^ 2) := by
  rw [large_remainder, constant_three, large_frobenius_sq]
  norm_num

end FrobeniusCp
