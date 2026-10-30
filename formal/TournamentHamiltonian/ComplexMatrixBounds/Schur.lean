module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! The rectangular Schur bound with independent row and column budgets. -/
noncomputable section
open Matrix
open scoped BigOperators NNReal Matrix.Norms.L2Operator

namespace ComplexMatrixBounds
variable {𝕜 ρ σ : Type*} [RCLike 𝕜] [Fintype ρ] [Fintype σ]

/-- Weighted Cauchy–Schwarz before taking square roots. -/
theorem row_column_mulVec_sq (A : Matrix ρ σ 𝕜) (R C : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C)
    (z : σ → 𝕜) :
    (∑ i, ‖(A *ᵥ z) i‖ ^ 2) ≤ (R * C) * ∑ j, ‖z j‖ ^ 2 := by
  have hpoint (i : ρ) : ‖(A *ᵥ z) i‖ ^ 2 ≤ R * ∑ j, ‖A i j‖ * ‖z j‖ ^ 2 := by
    have hnorm : ‖(A *ᵥ z) i‖ ≤ ∑ j, ‖A i j‖ * ‖z j‖ := by
      simpa only [Matrix.mulVec, dotProduct, norm_mul] using
        (norm_sum_le Finset.univ (fun j => A i j * z j))
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun j => ‖A i j‖ * ‖z j‖) (f := fun j => ‖A i j‖)
      (g := fun j => ‖A i j‖ * ‖z j‖ ^ 2) (fun _ _ => norm_nonneg _)
      (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)) (by
        intro j _
        exact le_of_eq (by ring))
    exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr hnorm |>.trans
        (h.trans (mul_le_mul_of_nonneg_right (hrow i)
          (Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)))))
  calc
    _ ≤ ∑ i, R * ∑ j, ‖A i j‖ * ‖z j‖ ^ 2 := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = R * ∑ j, (∑ i, ‖A i j‖) * ‖z j‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ R * ∑ j, C * ‖z j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hR
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Pointwise Euclidean form of Schur's estimate; either budget may be zero. -/
theorem schur_mulVec (A : Matrix ρ σ 𝕜) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C)
    (z : EuclideanSpace 𝕜 σ) :
    ‖(EuclideanSpace.equiv ρ 𝕜).symm (A *ᵥ z)‖ ≤ Real.sqrt (R * C) * ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hR hC), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  exact row_column_mulVec_sq A R C hR hrow hcol z

/-- The genuine L2 operator norm, not the entrywise or infinity matrix norm. -/
theorem schur_bound [DecidableEq σ] (A : Matrix ρ σ 𝕜) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ R) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ C) :
    ‖A‖ ≤ Real.sqrt (R * C) := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro z
  exact schur_mulVec A R C hR hC hrow hcol z

/-- Actual maximum absolute row sum, with value zero if there are no rows. -/
def rowMax (A : Matrix ρ σ 𝕜) : ℝ :=
  (Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) : ℝ≥0)

/-- Actual maximum absolute column sum, with value zero if there are no columns. -/
def columnMax (A : Matrix ρ σ 𝕜) : ℝ :=
  (Finset.univ.sup (fun j => ∑ i, ‖A i j‖₊) : ℝ≥0)

theorem rowMax_nonneg (A : Matrix ρ σ 𝕜) : 0 ≤ rowMax A := NNReal.coe_nonneg _
theorem columnMax_nonneg (A : Matrix ρ σ 𝕜) : 0 ≤ columnMax A := NNReal.coe_nonneg _

theorem row_sum_le_rowMax (A : Matrix ρ σ 𝕜) (i : ρ) : ∑ j, ‖A i j‖ ≤ rowMax A := by
  simpa only [rowMax, NNReal.coe_sum, coe_nnnorm] using
    (NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)))

theorem column_sum_le_columnMax (A : Matrix ρ σ 𝕜) (j : σ) : ∑ i, ‖A i j‖ ≤ columnMax A := by
  simpa only [columnMax, NNReal.coe_sum, coe_nnnorm] using
    (NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun j => ∑ i, ‖A i j‖₊) (Finset.mem_univ j)))

/-- The stored maximum has exactly the expected least-upper-bound property. -/
theorem rowMax_le_iff (A : Matrix ρ σ 𝕜) (R : ℝ) (hR : 0 ≤ R) :
    rowMax A ≤ R ↔ ∀ i, ∑ j, ‖A i j‖ ≤ R := by
  constructor
  · intro h i
    exact (row_sum_le_rowMax A i).trans h
  · intro h
    change ((Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) : ℝ≥0) : ℝ) ≤ R
    have hn : Finset.univ.sup (fun i => ∑ j, ‖A i j‖₊) ≤ (⟨R, hR⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i _
      apply NNReal.coe_le_coe.mp
      simp only [NNReal.coe_sum, coe_nnnorm]
      change (∑ j, ‖A i j‖) ≤ R
      exact h i
    exact NNReal.coe_le_coe.mpr hn

theorem columnMax_le_iff (A : Matrix ρ σ 𝕜) (C : ℝ) (hC : 0 ≤ C) :
    columnMax A ≤ C ↔ ∀ j, ∑ i, ‖A i j‖ ≤ C := by
  constructor
  · intro h j
    exact (column_sum_le_columnMax A j).trans h
  · intro h
    change ((Finset.univ.sup (fun j => ∑ i, ‖A i j‖₊) : ℝ≥0) : ℝ) ≤ C
    have hn : Finset.univ.sup (fun j => ∑ i, ‖A i j‖₊) ≤ (⟨C, hC⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro j _
      apply NNReal.coe_le_coe.mp
      simp only [NNReal.coe_sum, coe_nnnorm]
      change (∑ i, ‖A i j‖) ≤ C
      exact h j
    exact NNReal.coe_le_coe.mpr hn

/-- The literal sqrt(max-row-sum * max-column-sum) inequality. -/
theorem schur_max_bound [DecidableEq σ] (A : Matrix ρ σ 𝕜) :
    ‖A‖ ≤ Real.sqrt (rowMax A * columnMax A) :=
  schur_bound A _ _ (rowMax_nonneg A) (columnMax_nonneg A)
    (row_sum_le_rowMax A) (column_sum_le_columnMax A)

end ComplexMatrixBounds
