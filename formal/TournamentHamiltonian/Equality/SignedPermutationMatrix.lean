module

public import TournamentHamiltonian.Equality.SignedPermutationClassification

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

/-- One sign in each column at the permuted row: this is a signed permutation
matrix, explicitly and without an unproved membership predicate. -/
def signedPermutationMatrix {n : ℕ} (ε : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := (Matrix.diagonal ε).submatrix id e

theorem signedPermutationMatrix_apply {n : ℕ} (ε : Fin n → ℝ)
    (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    signedPermutationMatrix ε e i j = if i = e j then ε i else 0 := by
  simp [signedPermutationMatrix, Matrix.diagonal_apply]

/-- The pointwise switching/relabeling witness gives literal matrix conjugation. -/
theorem signedPermutationMatrix_conjugation {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (ε : Fin n → ℝ) (e : Equiv.Perm (Fin n)) :
    (signedPermutationMatrix ε e).transpose * S * signedPermutationMatrix ε e =
      (switch S ε).submatrix e e := by
  rw [signedPermutationMatrix, Matrix.transpose_submatrix, Matrix.diagonal_transpose]
  change (Matrix.diagonal ε).submatrix e (Equiv.refl _) *
      S.submatrix (Equiv.refl _) (Equiv.refl _) *
      (Matrix.diagonal ε).submatrix (Equiv.refl _) e = _
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← switch_eq_diagonal_mul]

theorem signedPermutationMatrix_orthogonal {n : ℕ} (ε : Fin n → ℝ)
    (hε : ∀ i, ε i ^ 2 = 1) (e : Equiv.Perm (Fin n)) :
    (signedPermutationMatrix ε e).transpose * signedPermutationMatrix ε e = 1 := by
  have hsw : switch (1 : Matrix (Fin n) (Fin n) ℝ) ε = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j; simpa [switch, pow_two] using hε i
    · simp [switch, hij]
  simpa [hsw] using signedPermutationMatrix_conjugation (1 : Matrix (Fin n) (Fin n) ℝ) ε e

/-- Literal `Ωᵀ S Ω = Tₙ` with an explicitly signed-permutation `Ω` and `ΩᵀΩ=I`.
All hypotheses concern actual fourth-order principal determinants. -/
theorem tournament_exists_signed_permutation_conjugation {n : ℕ}
    (T : Tournament n) (h4 : AllFourDetOne (signMatrix T)) :
    ∃ (ε : Fin n → ℝ) (e : Equiv.Perm (Fin n)),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (signedPermutationMatrix ε e).transpose * signedPermutationMatrix ε e = 1 ∧
      (signedPermutationMatrix ε e).transpose * signMatrix T * signedPermutationMatrix ε e =
        (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨ε, hε, e, he⟩ :=
    (tournament_allFourDetOne_iff_signedPermutationTransitive T).mp h4
  refine ⟨ε, e, hε, signedPermutationMatrix_orthogonal ε ?_ e, ?_⟩
  · intro i; rcases hε i with h | h <;> rw [h] <;> norm_num
  · rw [signedPermutationMatrix_conjugation, he]

/-- The only possible fourth principal determinants of a genuine tournament. -/
theorem tournament_four_det_eq_one_or_nine {n : ℕ} (T : Tournament n)
    (f : Fin 4 → Fin n) (hf : Function.Injective f) :
    ((signMatrix T).submatrix f f).det = 1 ∨
      ((signMatrix T).submatrix f f).det = 9 := by
  let S := signMatrix T
  have hS := signMatrix_isSkewSign T
  rw [det_skew_four (S.submatrix f f) (fun i j => hS.skew (f i) (f j))]
  have hsigns (i j : Fin 4) (hij : i ≠ j) := hS.signs (f i) (f j) (fun h => hij (hf h))
  simpa only [det_skewFour, Matrix.submatrix_apply] using
    det_skewFour_eq_one_or_nine (S (f 0) (f 1)) (S (f 0) (f 2)) (S (f 0) (f 3))
      (S (f 1) (f 2)) (S (f 1) (f 3)) (S (f 2) (f 3))
      (hsigns 0 1 (by decide)) (hsigns 0 2 (by decide)) (hsigns 0 3 (by decide))
      (hsigns 1 2 (by decide)) (hsigns 1 3 (by decide)) (hsigns 2 3 (by decide))

/-- Absence of bad fourth principal minors is an equivalent actual-tournament criterion. -/
theorem tournament_no_four_det_nine_iff_signedPermutationTransitive {n : ℕ}
    (T : Tournament n) :
    (∀ f : Fin 4 → Fin n, Function.Injective f → ((signMatrix T).submatrix f f).det ≠ 9) ↔
      SignedPermutationTransitive (signMatrix T) := by
  rw [← tournament_allFourDetOne_iff_signedPermutationTransitive T]
  constructor
  · intro h f hf
    exact (tournament_four_det_eq_one_or_nine T f hf).resolve_right (h f hf)
  · intro h f hf
    rw [h f hf]
    norm_num

end TournamentHamiltonian.Equality
