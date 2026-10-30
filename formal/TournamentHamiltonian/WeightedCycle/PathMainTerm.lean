module

public import TournamentHamiltonian.WeightedCycle.MainTerm

@[expose] public section

/-! Exact finite path main-term algebra. This uses the all-ones complement
`J - D`, not the tournament-only expression `I + D`. No asymptotics occur. -/
namespace WeightedCycle
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open TournamentHamiltonian
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Adding `s` on the constant direction multiplies the determinant by `1+s`. -/
theorem det_one_add_smul_constantProjection [Nonempty α] (s : ℝ) :
    (1 + s • (constantProjection : Matrix α α ℝ)).det = 1 + s := by
  simpa only [neg_smul, sub_neg_eq_add] using
    det_one_sub_smul_constantProjection (α := α) (-s)

omit [DecidableEq α] in
/-- The normalized constant projection is genuinely `J/N`, with `J` all ones. -/
theorem card_smul_constantProjection [Nonempty α] :
    (Fintype.card α : ℝ) • (constantProjection : Matrix α α ℝ) =
      Matrix.of (fun _ _ : α => (1 : ℝ)) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i j
  simp [constantProjection, hn]

/-- Exact path determinant main term for any real row-stochastic matrix. -/
theorem det_one_add_ones_sub_eq_card_mul_centered [Nonempty α]
    (D : Matrix α α ℝ) (hrow : ∀ i, ∑ j, D i j = 1) :
    (1 + Matrix.of (fun _ _ : α => (1 : ℝ)) - D).det =
      (Fintype.card α : ℝ) * (1 - centered D).det := by
  have hmul : (1 - centered D) *
      (1 + ((Fintype.card α : ℝ) - 1) • constantProjection) =
      (1 : Matrix α α ℝ) + Matrix.of (fun _ _ : α => (1 : ℝ)) - D := by
    simp only [sub_mul, mul_add, one_mul, mul_one, Matrix.mul_smul,
      centered_mul_constantProjection D hrow, smul_zero]
    rw [sub_smul, one_smul, card_smul_constantProjection]
    simp only [centered]
    abel
  rw [← hmul, Matrix.det_mul, det_one_add_smul_constantProjection]
  ring

/-- Sum of the actual all-ones-complement principal determinants. The empty
minor remains present and equals 1; the outer vertex type must be nonempty. -/
theorem path_main_term_eq_card_mul_centered_det [Nonempty α]
    (D : Matrix α α ℝ) (hrow : ∀ i, ∑ j, D i j = 1) :
    (∑ U : Finset α,
      ((Matrix.of (fun _ _ : α => (1 : ℝ)) - D).submatrix
        (Subtype.val : U → α) Subtype.val).det) =
      (Fintype.card α : ℝ) * (1 - centered D).det := by
  have h := matrix_principal_generating_det
    (Matrix.of (fun _ _ : α => (1 : ℝ)) - D) 1
  simp only [one_smul, one_pow, one_mul] at h
  rw [← h, ← add_sub_assoc]
  exact det_one_add_ones_sub_eq_card_mul_centered D hrow

end
end WeightedCycle
