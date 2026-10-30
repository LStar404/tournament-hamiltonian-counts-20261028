module

public import TournamentHamiltonian.DenseMinorBounds
public import Mathlib.LinearAlgebra.Matrix.Permanent

set_option autoImplicit false

@[expose] public section
namespace TournamentHamiltonian

/-- For nonnegative matrices, permutation terms are distinct terms of the product
of column sums. No nonempty-index or positivity hypothesis is required. -/
theorem permanent_le_prod_column_sums {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j) :
    Q.permanent ≤ ∏ j, ∑ i, Q i j := by
  classical
  rw [Matrix.permanent, Fintype.prod_sum]
  let f : Equiv.Perm ι → (ι → ι) := fun σ => σ
  have hf : Function.Injective f := by
    intro σ τ h
    exact Equiv.Perm.ext (congrFun h)
  calc
    (∑ σ : Equiv.Perm ι, ∏ i, Q (σ i) i) =
        ∑ g ∈ Finset.univ.image f, ∏ i, Q (g i) i := by
      rw [Finset.sum_image (fun σ _ τ _ h => hf h)]
    _ ≤ ∑ g : ι → ι, ∏ i, Q (g i) i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun g _ _ => Finset.prod_nonneg (fun i _ => hQ _ _))

/-- Row-sum version of the same elementary nonnegative permanent estimate. -/
theorem permanent_le_prod_row_sums {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j) :
    Q.permanent ≤ ∏ i, ∑ j, Q i j := by
  simpa only [Matrix.permanent_transpose, Matrix.transpose_apply] using
    permanent_le_prod_column_sums Q.transpose (fun i j => hQ j i)

theorem permanent_nonneg_of_entrywise {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j) : 0 ≤ Q.permanent := by
  classical
  exact Finset.sum_nonneg (fun σ _ => Finset.prod_nonneg (fun i _ => hQ _ _))

/-- Substochastic permanent bound, including the empty matrix with permanent 1. -/
theorem permanent_le_one_of_substochastic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : ∀ i j, 0 ≤ Q i j)
    (hrow : ∀ i, (∑ j, Q i j) ≤ 1) :
    0 ≤ Q.permanent ∧ Q.permanent ≤ 1 := by
  refine ⟨permanent_nonneg_of_entrywise Q hQ, (permanent_le_prod_row_sums Q hQ).trans ?_⟩
  exact Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg (fun j _ => hQ i j))
    (fun i _ => hrow i)

/-- Every actual complement principal minor is substochastic, for all deletion
sizes. In particular this does not assume the small-deletion threshold. -/
theorem DenseStochastic.minor_permanent_le_one {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (U : Finset (Fin n)) :
    0 ≤ (densePrincipalMinor D U).permanent ∧
      (densePrincipalMinor D U).permanent ≤ 1 := by
  apply permanent_le_one_of_substochastic
  · intro i j
    exact hD.nonnegative i j
  · intro i
    simpa only [densePrincipalMinor, Matrix.submatrix_apply, Finset.sum_coe_sort] using
      (hD.removed_row_bounds Uᶜ i).2.2

/-- Actual full deletion: no 0-dimensional boundary is discarded. -/
@[simp] theorem densePrincipalMinor_univ_permanent {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) :
    (densePrincipalMinor D Finset.univ).permanent = 1 := by
  classical
  let : IsEmpty ((Finset.univ : Finset (Fin n))ᶜ : Finset (Fin n)) :=
    Finset.isEmpty_coe_sort.mpr Finset.compl_univ
  exact Matrix.permanent_isEmpty

end TournamentHamiltonian
