module

public import TournamentHamiltonian.NonregularRate.PermanentRows

@[expose] public section

set_option autoImplicit false
namespace NonregularRate
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Finite induction rounds exactly the designated rows. All row capacities and
box constraints remain valid after each step, and the actual permanent increases. -/
theorem exists_round_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : Fin n → ℕ)
    (hR : ∀ i, R i ≤ n) (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)
    (hsum : ∀ i, ∑ j, A i j ≤ R i) (s : Finset (Fin n)) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, 0 ≤ B i j ∧ B i j ≤ 1) ∧
      (∀ i, ∑ j, B i j ≤ R i) ∧
      A.permanent ≤ B.permanent ∧
      (∀ i ∈ s, (∀ j, B i j = 0 ∨ B i j = 1) ∧ (∑ j, B i j) = R i) := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨A, hA, hsum, le_rfl, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨B, hB, hrows, hper, hdone⟩ := ih
    obtain ⟨C, hC, hinc, hCi, hCsum, hkeep⟩ :=
      exists_round_matrix_row B i (hR i) hB (hrows i)
    refine ⟨C, hC, ?_, hper.trans hinc, ?_⟩
    · intro k
      by_cases hk : k = i
      · subst k
        exact hCsum.le
      · rw [hkeep k hk]
        exact hrows k
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact ⟨hCi, hCsum⟩
      · have hki : k ≠ i := by
          intro he
          subst k
          exact hi hk
        rw [hkeep k hki]
        exact hdone k hk

/-- Weighted-row completion/rounding exists with exact integral targets and
without decreasing the permanent. Diagonal ones are deliberately allowed. -/
theorem exists_zeroOne_rounding {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : Fin n → ℕ)
    (hR : ∀ i, R i ≤ n) (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)
    (hsum : ∀ i, ∑ j, A i j ≤ R i) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, B i j = 0 ∨ B i j = 1) ∧
      (∀ i, ∑ j, B i j = R i) ∧ A.permanent ≤ B.permanent := by
  obtain ⟨B, _, _, hp, hdone⟩ := exists_round_rows A R hR hA hsum Finset.univ
  exact ⟨B, fun i j => (hdone i (Finset.mem_univ i)).1 j,
    fun i => (hdone i (Finset.mem_univ i)).2, hp⟩

theorem zeroOne_row_card {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) (i : Fin n) :
    ((Finset.univ.filter (fun j => A i j = 1)).card : ℝ) = ∑ j, A i j := by
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro j _
  rcases hA i j with hj | hj <;> simp [hj]

/-- Weighted Brégman with the existing zero-row convention. Also valid at n=0. -/
theorem weighted_permanent_le_bregman {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (R : Fin n → ℕ) (hR : ∀ i, R i ≤ n)
    (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)
    (hsum : ∀ i, ∑ j, A i j ≤ R i) :
    A.permanent ≤ ∏ i, bregmanRowFactor (R i) := by
  obtain ⟨B, hB, hs, hp⟩ := exists_zeroOne_rounding A R hR hA hsum
  have hc (i : Fin n) : (Finset.univ.filter (fun j => B i j = 1)).card = R i := by
    have he := (zeroOne_row_card B hB i).trans (hs i)
    exact_mod_cast he
  apply hp.trans
  simpa only [hc] using zeroOneMatrix_permanent_le_bregman B hB

/-- The requested explicit weighted Brégman inequality for positive integral
row targets. No rounding or permanent estimate occurs among its hypotheses. -/
theorem weighted_permanent_le_factorial_product {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (R : Fin n → ℕ) (hR : ∀ i, 1 ≤ R i ∧ R i ≤ n)
    (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)
    (hsum : ∀ i, ∑ j, A i j ≤ R i) :
    A.permanent ≤ ∏ i, ((R i).factorial : ℝ) ^ ((1 : ℝ) / R i) := by
  have h := weighted_permanent_le_bregman A R (fun i => (hR i).2) hA hsum
  have hf (i : Fin n) : bregmanRowFactor (R i) = ((R i).factorial : ℝ)^((1 : ℝ)/R i) := by
    rw [bregmanRowFactor, ite_eq_right (by have := (hR i).1; omega)]
  simpa only [hf] using h

/-- Label-independent weighted Brégman, directly usable for product vertex types. -/
theorem weighted_permanent_le_factorial_product_fintype {α : Type*}
    [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) (R : α → ℕ)
    (hR : ∀ i, 1 ≤ R i ∧ R i ≤ Fintype.card α)
    (hA : ∀ i j, 0 ≤ A i j ∧ A i j ≤ 1)
    (hsum : ∀ i, ∑ j, A i j ≤ R i) :
    A.permanent ≤ ∏ i, ((R i).factorial : ℝ)^((1 : ℝ)/R i) := by
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let A' : Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℝ :=
    fun i j => A (e.symm i) (e.symm j)
  let R' : Fin (Fintype.card α) → ℕ := fun i => R (e.symm i)
  have hp : A.permanent = A'.permanent := by
    unfold Matrix.permanent
    apply Fintype.sum_equiv (Equiv.permCongr e)
    intro σ
    apply Fintype.prod_equiv e
    intro i
    simp [A', Equiv.permCongr_apply]
  have hs (i : Fin (Fintype.card α)) : ∑ j, A' i j ≤ R' i := by
    change (∑ j, A (e.symm i) (e.symm j)) ≤ R (e.symm i)
    rw [Equiv.sum_comp e.symm]
    exact hsum (e.symm i)
  calc
    A.permanent = A'.permanent := hp
    _ ≤ ∏ i, ((R' i).factorial : ℝ)^((1 : ℝ)/R' i) :=
      weighted_permanent_le_factorial_product A' R' (fun i => hR (e.symm i))
        (fun i j => hA (e.symm i) (e.symm j)) hs
    _ = _ := by
      symm
      apply Fintype.prod_equiv e
      intro i
      simp [R']

end
end NonregularRate
