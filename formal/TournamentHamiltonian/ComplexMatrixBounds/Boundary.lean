module

public import TournamentHamiltonian.ComplexMatrixBounds.Schur
public import TournamentHamiltonian.ComplexMatrixBounds.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-! Kernel-checked boundary and norm-convention tests. -/
noncomputable section
open Matrix
open scoped BigOperators NNReal Matrix.Norms.L2Operator

namespace ComplexMatrixBounds

/-- A zero row budget forces the genuine operator norm to vanish. -/
theorem zero_row_budget {ρ σ : Type*} [Fintype ρ] [Fintype σ] [DecidableEq σ]
    (A : Matrix ρ σ ℂ) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ 0) : ‖A‖ = 0 := by
  have h := schur_bound A 0 (columnMax A) (by rfl) (columnMax_nonneg A)
    hrow (column_sum_le_columnMax A)
  simp only [zero_mul, Real.sqrt_zero] at h
  exact le_antisymm h (norm_nonneg A)

/-- The separate zero column budget is also allowed, without division by a budget. -/
theorem zero_column_budget {ρ σ : Type*} [Fintype ρ] [Fintype σ] [DecidableEq σ]
    (A : Matrix ρ σ ℂ) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ 0) : ‖A‖ = 0 := by
  have h := schur_bound A (rowMax A) 0 (rowMax_nonneg A) (by rfl)
    (row_sum_le_rowMax A) hcol
  simp only [mul_zero, Real.sqrt_zero] at h
  exact le_antisymm h (norm_nonneg A)

theorem empty_rows (A : Matrix (Fin 0) (Fin 2) ℂ) :
    ‖A‖ = 0 ∧ rowMax A = 0 ∧ columnMax A = 0 := by
  have h : A = 0 := Subsingleton.elim _ _
  subst A
  simp [rowMax, columnMax]

theorem empty_columns (A : Matrix (Fin 2) (Fin 0) ℂ) :
    ‖A‖ = 0 ∧ rowMax A = 0 ∧ columnMax A = 0 := by
  have h : A = 0 := Subsingleton.elim _ _
  subst A
  simp [rowMax, columnMax]

theorem hadamard_empty (A : Matrix (Fin 0) (Fin 0) ℂ) :
    ‖A.det‖ = 1 ∧ (∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2)) = 1 := by simp

theorem hadamard_single (z : ℂ) :
    ‖(!![z] : Matrix (Fin 1) (Fin 1) ℂ).det‖ =
      ∏ i : Fin 1, Real.sqrt (∑ j : Fin 1, ‖(!![z] : Matrix (Fin 1) (Fin 1) ℂ) i j‖ ^ 2) := by
  simp

/-- Unequal row/column budgets: the true bound is sqrt(2), not max(2,1)=2. -/
def rectangularExample : Matrix (Fin 1) (Fin 2) ℂ := !![1, Complex.I]

theorem rectangular_budgets : rowMax rectangularExample = 2 ∧
    columnMax rectangularExample = 1 := by
  norm_num [rowMax, columnMax, rectangularExample, Fin.sum_univ_two, Finset.univ_fin2]

theorem rectangular_schur : ‖rectangularExample‖ ≤ Real.sqrt 2 := by
  simpa only [rectangular_budgets.1, rectangular_budgets.2, mul_one] using
    schur_max_bound rectangularExample

/-- Direct Gram-matrix check that the rectangular example attains the L2 bound. -/
theorem rectangular_norm_exact : ‖rectangularExample‖ = Real.sqrt 2 := by
  have hAA : rectangularExample * rectangularExampleᴴ =
      (2 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [rectangularExample, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self rectangularExampleᴴ
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, hAA] at h
  norm_num at h
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith

theorem rectangular_strict_improvement : Real.sqrt (rowMax rectangularExample *
    columnMax rectangularExample) < max (rowMax rectangularExample) (columnMax rectangularExample) := by
  rw [rectangular_budgets.1, rectangular_budgets.2]
  norm_num

/-- A genuinely non-normal complex matrix, not a diagonal/spectral special case. -/
def nonNormalExample : Matrix (Fin 2) (Fin 2) ℂ := !![1, Complex.I; 0, 1]

theorem nonNormalExample_not_normal :
    nonNormalExample * nonNormalExampleᴴ ≠ nonNormalExampleᴴ * nonNormalExample := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  norm_num [nonNormalExample, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] at h00

theorem nonNormalExample_hadamard : ‖nonNormalExample.det‖ = 1 ∧
    (∏ i, Real.sqrt (∑ j, ‖nonNormalExample i j‖ ^ 2)) = Real.sqrt 2 ∧
    ‖nonNormalExample.det‖ ≤ Real.sqrt 2 := by
  have h := hadamard nonNormalExample
  norm_num [nonNormalExample, Matrix.det_fin_two, Fin.prod_univ_two, Fin.sum_univ_two] at h ⊢

/-- An actual zero row makes both sides zero, including a nonzero complex second row. -/
def zeroRowExample : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, Complex.I]

theorem zeroRowExample_hadamard : ‖zeroRowExample.det‖ = 0 ∧
    (∏ i, Real.sqrt (∑ j, ‖zeroRowExample i j‖ ^ 2)) = 0 := by
  norm_num [zeroRowExample, Matrix.det_fin_two, Fin.prod_univ_two, Fin.sum_univ_two]

/-- A complex orthogonal-row equality case has determinant modulus two. -/
def equalityExample : Matrix (Fin 2) (Fin 2) ℂ := !![1, Complex.I; Complex.I, 1]

theorem equalityExample_hadamard : ‖equalityExample.det‖ = 2 ∧
    (∏ i, Real.sqrt (∑ j, ‖equalityExample i j‖ ^ 2)) = 2 := by
  norm_num [equalityExample, Matrix.det_fin_two, Fin.prod_univ_two, Fin.sum_univ_two,
    Complex.I_sq, ← sq, Real.sq_sqrt]

end ComplexMatrixBounds
