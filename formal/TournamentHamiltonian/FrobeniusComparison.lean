module

public import TournamentHamiltonian.VectorDomination
public import TournamentHamiltonian.ComparisonConjugation
public import TournamentHamiltonian.TransitiveShift
public import TournamentHamiltonian.SpectralPowerMoments

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

/-- Every power of a bounded real skew matrix has Frobenius mass at most
the corresponding power of the transitive sign matrix. -/
theorem skew_pow_frob_le_transitive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hskew : A.transpose = -A) (hentry : ∀ i j, |A i j| ≤ 1) (p : ℕ) :
    matrixFrobSq (A ^ p) ≤ matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ p) := by
  calc
    _ = ∑ j, ∑ i, (A ^ p) i j ^ 2 := Finset.sum_comm
    _ ≤ ∑ _j : Fin n, ∑ i, ((comparisonMatrix n) ^ p) i ⟨0, hn⟩ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact skew_pow_column_sq_le_comparison A hn hskew hentry p j
    _ = (n : ℝ) * (∑ i, ((comparisonMatrix n) ^ p) i ⟨0, hn⟩ ^ 2) := by simp
    _ = (n : ℝ) * (((-((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 2)) ^ p)
        ⟨0, hn⟩ ⟨0, hn⟩) := by
      rw [comparison_pow_first_column_sq_eq_transitive_gram n hn p]
    _ = _ := (transitive_frob_pow_eq_card_mul_diag n hn p).symm

theorem signMatrix_entry_abs_le_one {n : ℕ} (T : Tournament n) (i j : Fin n) :
    |signMatrix T i j| ≤ 1 := by
  by_cases hij : i = j
  · subst j
    simp [signMatrix]
  · cases h : T.val i j <;> norm_num [signMatrix, hij, h]

/-- The formerly outstanding finite comparison, with all multiplicities and
normalization inherited from the actual tournament spectrum. -/
theorem pairedMasses_pow_sum_le_alternating {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (p : ℕ) (hp : 0 < p) :
    ((pairedMasses T).map (fun x => x ^ p)).sum ≤
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ p)).sum := by
  rw [pairedMasses_pow_sum_eq_frob T hn p hp,
    pairedMasses_pow_sum_eq_frob (alternatingTournament n) hn p hp]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [matrixFrobSq_alternating_pow n p, signMatrix_transitiveTournament]
  exact skew_pow_frob_le_transitive (signMatrix T) hn (signMatrix_transpose T)
    (signMatrix_entry_abs_le_one T) p

theorem pairedMasses_odd_pow_sum_le_alternating {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (k : ℕ) :
    ((pairedMasses T).map (fun x => x ^ (2 * k + 1))).sum ≤
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ (2 * k + 1))).sum :=
  pairedMasses_pow_sum_le_alternating T hn (2 * k + 1) (by omega)

end TournamentHamiltonian
