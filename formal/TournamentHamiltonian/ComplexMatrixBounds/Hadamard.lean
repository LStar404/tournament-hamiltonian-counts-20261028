module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

/-! Actual Hadamard row-product bound, valid also for singular and zero-dimensional matrices. -/

noncomputable section
open scoped BigOperators

namespace ComplexMatrixBounds

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Changing between orthonormal bases preserves the modulus of the actual determinant
of an arbitrary family; no independence of that family is assumed. -/
theorem norm_basis_det_eq {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (a b : OrthonormalBasis ι 𝕜 E) (f : ι → E) :
    ‖a.toBasis.det f‖ = ‖b.toBasis.det f‖ := by
  have h := congrArg (fun g : E [⋀^ι]→ₗ[𝕜] 𝕜 => g f)
    (a.toBasis.det.eq_smul_basis_det b.toBasis)
  change a.toBasis.det f = a.toBasis.det b * b.toBasis.det f at h
  rw [h, norm_mul, a.det_to_matrix_orthonormalBasis b, one_mul]

/-- Hadamard for an indexed family in a finite-dimensional inner product space. -/
theorem norm_basis_det_le_prod {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (a : OrthonormalBasis (Fin n) 𝕜 E) (f : Fin n → E) :
    ‖a.toBasis.det f‖ ≤ ∏ i, ‖f i‖ := by
  have hdim : Module.finrank 𝕜 E = Fintype.card (Fin n) := Module.finrank_eq_card_basis a.toBasis
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  rw [norm_basis_det_eq a b f,
    InnerProductSpace.gramSchmidtOrthonormalBasis_det hdim f, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  simpa only [b.orthonormal.norm_eq_one i, one_mul] using norm_inner_le_norm (b i) (f i)

/-- Actual complex/real finite matrix determinant bounded by the product of its row L2 norms. -/
theorem hadamard_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  let b := EuclideanSpace.basisFun (Fin n) 𝕜
  let f : Fin n → EuclideanSpace 𝕜 (Fin n) := fun i => WithLp.toLp 2 (A.row i)
  have h := norm_basis_det_le_prod b f
  have hm : b.toBasis.toMatrix f = A.transpose := by
    ext i j
    simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      b, f, EuclideanSpace.basisFun_repr, Matrix.row, Matrix.transpose_apply]
  rw [Module.Basis.det_apply, hm, Matrix.det_transpose] at h
  simpa [f, EuclideanSpace.norm_eq, Matrix.row] using h

/-- Hadamard row bound for arbitrary finite index types, including the empty type. -/
theorem hadamard {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  let e := (Fintype.equivFin ι).symm
  have h := hadamard_fin (A.submatrix e e)
  rw [Matrix.det_submatrix_equiv_self] at h
  convert h using 1
  symm
  apply Fintype.prod_equiv e
  intro i
  congr 1
  apply Fintype.sum_equiv e
  intro j
  rfl

/-- The literal Gram determinant identity uses complex conjugate transpose. -/
theorem det_mul_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : (A * A.conjTranspose).det = ((‖A.det‖ : 𝕜) ^ 2) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  exact RCLike.mul_conj A.det

/-- The squared row bound, before taking square roots. -/
theorem hadamard_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg A.det) (hadamard A) 2
  simpa only [← Finset.prod_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] using h

/-- Transposing gives the corresponding actual column-product inequality. -/
theorem hadamard_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) := by
  simpa only [Matrix.det_transpose, Matrix.transpose_apply] using hadamard A.transpose

end ComplexMatrixBounds
