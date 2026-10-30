module

public import TournamentHamiltonian.BlockMatrix.Gap

set_option autoImplicit false
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator
namespace UniformBlockMatrix
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem euclidean_norm_comp_equiv (e : ι ≃ κ) (x : EuclideanSpace ℝ κ) :
    ‖WithLp.toLp 2 (fun i => x (e i))‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖x (e i)‖ ^ 2) = ∑ j, ‖x j‖ ^ 2
  exact e.sum_comp (fun j => ‖x j‖ ^ 2)

theorem submatrix_equiv_opNorm_le (A : Matrix κ κ ℝ) (e : ι ≃ κ) :
    ‖A.submatrix e e‖ ≤ ‖A‖ := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y : EuclideanSpace ℝ κ := WithLp.toLp 2 (fun j => x (e.symm j))
  have hxy : ‖y‖ = ‖x‖ := euclidean_norm_comp_equiv e.symm x
  have hact : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (A.submatrix e e) x =
      WithLp.toLp 2 (fun i => (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℝ) A y) (e i)) := by
    ext i
    change (∑ j : ι, A (e i) (e j) * x j) = ∑ j : κ, A (e i) j * y j
    simpa [y] using e.sum_comp (fun j => A (e i) j * x (e.symm j))
  rw [hact, euclidean_norm_comp_equiv]
  have h := ContinuousLinearMap.le_opNorm
    (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℝ) A) y
  simpa only [Matrix.l2_opNorm_toEuclideanCLM, hxy] using h

/-- Reindexing by a genuine equivalence preserves the real L2 matrix norm. -/
theorem submatrix_equiv_opNorm_eq (A : Matrix κ κ ℝ) (e : ι ≃ κ) :
    ‖A.submatrix e e‖ = ‖A‖ := by
  apply le_antisymm (submatrix_equiv_opNorm_le A e)
  have h := submatrix_equiv_opNorm_le (A.submatrix e e) e.symm
  simpa [Matrix.submatrix_submatrix] using h

/-- Reindex the actual block density to the `Fin (d*m)` interface. -/
def densityFin {d m : ℕ} (T : TournamentHamiltonian.Tournament d) :
    Matrix (Fin (d * m)) (Fin (d * m)) ℝ :=
  (density (m := m) T).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The fixed class is invariant under relabelling. -/
theorem FixedDenseClass.submatrix_equiv {D : Matrix κ κ ℝ} (hD : FixedDenseClass D)
    (e : ι ≃ κ) : FixedDenseClass (D.submatrix e e) where
  nonneg i j := hD.nonneg (e i) (e j)
  row_sum i := by
    change (∑ j, D (e i) (e j)) = 1
    rw [e.sum_comp]
    exact hD.row_sum (e i)
  col_sum j := by
    change (∑ i, D (e i) (e j)) = 1
    rw [e.sum_comp (fun i => D i (e j))]
    exact hD.col_sum (e j)
  entry_le i j := by
    simpa only [Fintype.card_congr e, Matrix.submatrix_apply] using hD.entry_le (e i) (e j)
  gap := by
    have heq : D.submatrix e e - (1 / (Fintype.card ι : ℝ)) • ones ι =
        (D - (1 / (Fintype.card κ : ℝ)) • ones κ).submatrix e e := by
      ext i j
      simp [Matrix.submatrix_apply, ones, Fintype.card_congr e]
    rw [heq, submatrix_equiv_opNorm_eq]
    exact hD.gap

theorem densityFin_mem_fixedDenseClass {d m : ℕ} (T : TournamentHamiltonian.Tournament d)
    (hT : IsRegular T) (hN : 20 ≤ d * m) : FixedDenseClass (densityFin (m := m) T) :=
  (density_mem_fixedDenseClass T hT hN).submatrix_equiv finProdFinEquiv.symm

end
end UniformBlockMatrix
