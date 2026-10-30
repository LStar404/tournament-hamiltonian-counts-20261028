module

public import TournamentHamiltonian.Equality.PowerEqualityDescent

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open scoped BigOperators Matrix

/-- The exact paired-mass normalization transfers equality to actual matrix
Frobenius powers; the common denominator is 2*n^(2p), not n^p. -/
theorem sign_frob_pow_eq_of_pairedMasses_pow_eq {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (p : ℕ) (hp : 0 < p)
    (heq : ((pairedMasses T).map (fun x => x ^ p)).sum =
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ p)).sum) :
    matrixFrobSq ((signMatrix T) ^ p) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ p) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hd : 2 * (n : ℝ) ^ (2 * p) ≠ 0 := ne_of_gt (by positivity)
  rw [pairedMasses_pow_sum_eq_frob T hn p hp,
    pairedMasses_pow_sum_eq_frob (alternatingTournament n) hn p hp,
    matrixFrobSq_alternating_pow, signMatrix_transitiveTournament] at heq
  exact (div_left_inj' hd).mp heq

/-- Equality in any positive paired moment propagates to all smaller positive
moments. The actual finite spectrum and all multiplicities are retained. -/
theorem pairedMasses_pow_eq_of_le_of_eq {n : ℕ} (hn : 2 ≤ n) (T : Tournament n)
    (p q : ℕ) (hq : 0 < q) (hqp : q ≤ p)
    (heq : ((pairedMasses T).map (fun x => x ^ p)).sum =
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ p)).sum) :
    ((pairedMasses T).map (fun x => x ^ q)).sum =
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ q)).sum := by
  have hn0 : 0 < n := by omega
  have hp : 0 < p := by omega
  have hf := sign_frob_pow_eq_of_pairedMasses_pow_eq T hn0 p hp heq
  have hqf := skew_frob_eq_of_le_of_eq hn (signMatrix T) (signMatrix_transpose T)
    (signMatrix_entry_abs_le_one T) p q hqp hf
  rw [pairedMasses_pow_sum_eq_frob T hn0 q hq,
    pairedMasses_pow_sum_eq_frob (alternatingTournament n) hn0 q hq,
    matrixFrobSq_alternating_pow, signMatrix_transitiveTournament, hqf]

/-- Strictness of any positive paired moment propagates upward. -/
theorem pairedMasses_pow_lt_of_le_of_lt {n : ℕ} (hn : 2 ≤ n) (T : Tournament n)
    (p q : ℕ) (hq : 0 < q) (hqp : q ≤ p)
    (hlt : ((pairedMasses T).map (fun x => x ^ q)).sum <
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ q)).sum) :
    ((pairedMasses T).map (fun x => x ^ p)).sum <
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ p)).sum := by
  have hle := pairedMasses_pow_sum_le_alternating T (by omega) p (by omega)
  rcases lt_or_eq_of_le hle with hlt' | heq
  · exact hlt'
  · exact False.elim ((ne_of_lt hlt) (pairedMasses_pow_eq_of_le_of_eq hn T p q hq hqp heq))

/-- Any paired-moment equality at p >= 2 forces the p=2 Frobenius equality.
This is an input for, not a proof of, switching/transitive classification. -/
theorem sign_frob_sq_eq_of_pairedMasses_pow_eq {n : ℕ} (hn : 2 ≤ n) (T : Tournament n)
    (p : ℕ) (hp : 2 ≤ p)
    (heq : ((pairedMasses T).map (fun x => x ^ p)).sum =
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ p)).sum) :
    matrixFrobSq ((signMatrix T) ^ 2) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 2) := by
  exact skew_frob_eq_of_le_of_eq hn (signMatrix T) (signMatrix_transpose T)
    (signMatrix_entry_abs_le_one T) p 2 hp
    (sign_frob_pow_eq_of_pairedMasses_pow_eq T (by omega) p (by omega) heq)

/-- A strict p=2 Frobenius comparison yields strictness of every paired moment
p >= 2, including all odd powers at least three. No classification is assumed
except through the explicitly displayed p=2 strictness premise. -/
theorem pairedMasses_pow_lt_of_sign_frob_sq_lt {n : ℕ} (hn : 2 ≤ n) (T : Tournament n)
    (p : ℕ) (hp : 2 ≤ p)
    (hlt : matrixFrobSq ((signMatrix T) ^ 2) <
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 2)) :
    ((pairedMasses T).map (fun x => x ^ p)).sum <
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ p)).sum := by
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hf := skew_frob_lt_of_le_of_lt hn (signMatrix T) (signMatrix_transpose T)
    (signMatrix_entry_abs_le_one T) p 2 hp hlt
  rw [pairedMasses_pow_sum_eq_frob T hn0 p (by omega),
    pairedMasses_pow_sum_eq_frob (alternatingTournament n) hn0 p (by omega),
    matrixFrobSq_alternating_pow, signMatrix_transitiveTournament]
  exact div_lt_div_of_pos_right hf (by positivity)

end TournamentHamiltonian
