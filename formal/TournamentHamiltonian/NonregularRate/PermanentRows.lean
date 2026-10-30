module

public import TournamentHamiltonian.NonregularRate.RowRounding

@[expose] public section

set_option autoImplicit false
namespace NonregularRate
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Replace a single actual matrix row. -/
def replaceRow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun k j => if k = i then w j else A k j

@[simp] theorem replaceRow_same {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (w : Fin n → ℝ) : replaceRow A i w i = w := by
  funext j
  simp [replaceRow]

theorem replaceRow_of_ne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (w : Fin n → ℝ) (k : Fin n) (hk : k ≠ i) :
    replaceRow A i w k = A k := by
  funext j
  simp [replaceRow, hk]

@[simp] theorem replaceRow_eq_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : replaceRow A i (A i) = A := by
  ext k j
  by_cases hk : k = i <;> simp [replaceRow, hk]

/-- The coefficient of entry (i,j) in the permanent with all other rows fixed.
It is an explicit finite sum of products of actual off-row entries. -/
def rowCofactor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), if σ i = j then
    ∏ k ∈ (Finset.univ.erase i), A k (σ k) else 0

theorem rowCofactor_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (i j : Fin n) : 0 ≤ rowCofactor A i j := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact Finset.prod_nonneg fun k _ => hA k (σ k)
  · rfl

/-- The permanent is genuinely linear in the replacement row. -/
theorem permanent_update_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (w : Fin n → ℝ) :
    (replaceRow A i w).permanent = ∑ j, w j * rowCofactor A i j := by
  rw [← Matrix.permanent_transpose, Matrix.permanent]
  change (∑ σ : Equiv.Perm (Fin n), ∏ k, replaceRow A i w k (σ k)) = _
  have hp (σ : Equiv.Perm (Fin n)) :
      (∏ k, replaceRow A i w k (σ k)) =
        w (σ i) * ∏ k ∈ (Finset.univ.erase i), A k (σ k) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [replaceRow_same]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [replaceRow_of_ne A i w k (Finset.ne_of_mem_erase hk)]
  simp_rw [hp]
  simp only [rowCofactor, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp

theorem permanent_row_expansion {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : A.permanent = ∑ j, A i j * rowCofactor A i j := by
  simpa only [replaceRow_eq_self] using permanent_update_row A i (A i)

/-- One actual row can be made zero-one with the exact target cardinality
without decreasing the permanent or changing any other row. -/
theorem exists_round_matrix_row {n R : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) (hR : R ≤ n) (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)
    (hsum : ∑ j, A i j ≤ R) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      (∀ k j, 0 ≤ B k j ∧ B k j ≤ 1) ∧
      A.permanent ≤ B.permanent ∧
      (∀ j, B i j = 0 ∨ B i j = 1) ∧
      (∑ j, B i j) = R ∧
      (∀ k, k ≠ i → B k = A k) := by
  obtain ⟨w, hw, hs, hdot⟩ := exists_round_row hR (A i) (rowCofactor A i)
    (hA i) hsum (rowCofactor_nonneg A (fun k j => (hA k j).1) i)
  refine ⟨replaceRow A i w, ?_, ?_, ?_, ?_, ?_⟩
  · intro k j
    by_cases hk : k = i
    · subst k
      simp only [replaceRow_same]
      rcases hw j with hj | hj <;> simp [hj]
    · simpa only [replaceRow_of_ne A i w k hk] using hA k j
  · rw [permanent_update_row, permanent_row_expansion A i]
    exact hdot
  · simpa only [replaceRow_same] using hw
  · simpa only [replaceRow_same] using hs
  · intro k hk
    exact replaceRow_of_ne A i w k hk

end
end NonregularRate
