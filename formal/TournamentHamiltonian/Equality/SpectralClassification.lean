module

public import TournamentHamiltonian.Equality.FourthMomentCriterion
public import TournamentHamiltonian.Equality.SixthMomentDivisibility
public import TournamentHamiltonian.Equality.SpectralRatioEquality

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

open scoped BigOperators Matrix

theorem matrixFrobSq_switch {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : Fin n → ℝ) (hε : ∀ i, ε i ^ 2 = 1) : matrixFrobSq (switch A ε) = matrixFrobSq A := by
  unfold matrixFrobSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp [switch, mul_pow, hε]

theorem switch_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (ε : Fin n → ℝ) (hε : ∀ i, ε i ^ 2 = 1) (p : ℕ) :
    (switch A ε) ^ p = switch (A ^ p) ε := by
  have hD : (Matrix.diagonal ε) * (Matrix.diagonal ε) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.one_apply, ← pow_two, hε]
    · simp [Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.one_apply, hij]
  simp only [switch_eq_diagonal_mul]
  exact spectral_involutive_conjugation_pow _ _ hD p

theorem matrixFrobSq_submatrix_equiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (e : Equiv.Perm (Fin n)) : matrixFrobSq (A.submatrix e e) = matrixFrobSq A := by
  unfold matrixFrobSq
  simp only [Matrix.submatrix_apply]
  calc
    _ = ∑ i, ∑ j, A (e i) j ^ 2 := by
      apply Finset.sum_congr rfl; intro i _
      exact Equiv.sum_comp e (fun j => A (e i) j ^ 2)
    _ = _ := Equiv.sum_comp e (fun i => ∑ j, A i j ^ 2)

/-- Signed permutations preserve every Frobenius power mass, not path counts. -/
theorem frob_pow_eq_of_signedPermutationTransitive {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : SignedPermutationTransitive A) (p : ℕ) :
    matrixFrobSq (A ^ p) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ p) := by
  obtain ⟨ε, hε, e, he⟩ := hA
  have hεsq (i : Fin n) : ε i ^ 2 = 1 := by
    rcases hε i with h | h <;> rw [h] <;> norm_num
  calc
    _ = matrixFrobSq ((switch A ε) ^ p) := by
      rw [switch_pow A ε hεsq]
      exact (matrixFrobSq_switch _ ε hεsq).symm
    _ = matrixFrobSq (((switch A ε) ^ p).submatrix e e) :=
      (matrixFrobSq_submatrix_equiv _ e).symm
    _ = _ := by rw [comparison_submatrix_pow, he]

theorem spectralRatio_eq_of_signedPermutationTransitive {n : ℕ} (T : Tournament n)
    (hn : 0 < n) (hT : SignedPermutationTransitive (signMatrix T)) :
    spectralRatio T = spectralRatio (alternatingTournament n) := by
  have hm (k : ℕ) : ((pairedMasses T).map (fun x => x ^ (2 * k + 1))).sum =
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ (2 * k + 1))).sum := by
    rw [pairedMasses_pow_sum_eq_frob T hn _ (by omega),
      pairedMasses_pow_sum_eq_frob (alternatingTournament n) hn _ (by omega),
      matrixFrobSq_alternating_pow, signMatrix_transitiveTournament,
      frob_pow_eq_of_signedPermutationTransitive hT]
  exact le_antisymm
    (spectralRatio_le_of_odd_paired_moments T _ hn (fun k => (hm k).le))
    (spectralRatio_le_of_odd_paired_moments _ T hn (fun k => (hm k).symm.le))

theorem tournament_eq_of_card_le_one {n : ℕ} (hn : n ≤ 1) (T U : Tournament n) : T = U := by
  apply Subtype.ext
  funext i j
  have hij : i = j := Fin.ext (by omega)
  subst j
  rw [T.property.1, U.property.1]

/-- End-to-end exact spectral classification, including zero and singleton orders.
The finite comparison, equality descent, fourth-minor criterion, and switching
classification are all discharged internally. -/
theorem spectralRatio_eq_iff_signedPermutationTransitive {n : ℕ} (T : Tournament n) :
    spectralRatio T = spectralRatio (alternatingTournament n) ↔
      SignedPermutationTransitive (signMatrix T) := by
  by_cases hn : 2 ≤ n
  · constructor
    · intro heq
      apply (tournament_allFourDetOne_iff_signedPermutationTransitive T).mp
      apply (tournament_frob_sq_eq_transitive_iff_allFourDetOne T).mp
      exact sign_frob_sq_eq_of_spectralRatio_eq hn T heq
    · exact spectralRatio_eq_of_signedPermutationTransitive T (by omega)
  · have heq : T = alternatingTournament n := tournament_eq_of_card_le_one (by omega) _ _
    rw [heq]
    exact ⟨fun _ => (tournament_allFourDetOne_iff_signedPermutationTransitive _).mp
      (allFourDetOne_alternatingTournament n), fun _ => rfl⟩

theorem two_le_of_not_signedPermutationTransitive {n : ℕ} (T : Tournament n)
    (hT : ¬ SignedPermutationTransitive (signMatrix T)) : 2 ≤ n := by
  by_contra hn
  have heq : T = alternatingTournament n := tournament_eq_of_card_le_one (by omega) _ _
  apply hT
  rw [heq]
  exact (tournament_allFourDetOne_iff_signedPermutationTransitive _).mp
    (allFourDetOne_alternatingTournament n)

theorem sign_frob_sq_lt_of_not_signedPermutationTransitive {n : ℕ} (T : Tournament n)
    (hT : ¬ SignedPermutationTransitive (signMatrix T)) :
    matrixFrobSq ((signMatrix T) ^ 2) <
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 2) := by
  have hn := two_le_of_not_signedPermutationTransitive T hT
  have hle := skew_pow_frob_le_transitive (signMatrix T) (by omega)
    (signMatrix_transpose T) (signMatrix_entry_abs_le_one T) 2
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact False.elim (hT ((tournament_allFourDetOne_iff_signedPermutationTransitive T).mp
      ((tournament_frob_sq_eq_transitive_iff_allFourDetOne T).mp heq)))

theorem spectralRatio_lt_iff_not_signedPermutationTransitive {n : ℕ} (T : Tournament n) :
    spectralRatio T < spectralRatio (alternatingTournament n) ↔
      ¬ SignedPermutationTransitive (signMatrix T) := by
  constructor
  · intro hlt hclass
    exact (ne_of_lt hlt) ((spectralRatio_eq_iff_signedPermutationTransitive T).mpr hclass)
  · intro hclass
    exact spectralRatio_lt_of_sign_frob_sq_lt
      (two_le_of_not_signedPermutationTransitive T hclass) T
      (sign_frob_sq_lt_of_not_signedPermutationTransitive T hclass)

/-- The sixth-moment arithmetic gap now has only the actual non-extremal class
condition: strict comparison is proved internally, not a caller premise. -/
theorem sixth_moment_gap_sixteen_of_not_signedPermutationTransitive {n : ℕ}
    (T : Tournament n) (hT : ¬ SignedPermutationTransitive (signMatrix T)) :
    16 ≤ matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 3) -
      matrixFrobSq ((signMatrix T) ^ 3) := by
  apply transitive_sixth_moment_gap_at_least_sixteen T
  exact skew_frob_lt_of_le_of_lt (two_le_of_not_signedPermutationTransitive T hT)
    (signMatrix T) (signMatrix_transpose T) (signMatrix_entry_abs_le_one T) 3 2 (by omega)
    (sign_frob_sq_lt_of_not_signedPermutationTransitive T hT)

theorem carousel_spectralRatio_eq_alternating (m : ℕ) :
    spectralRatio (carouselTournament m) = spectralRatio (alternatingTournament (2 * m + 1)) := by
  apply Complex.ofReal_injective
  rw [carousel_spectralRatio_eq, alternating_spectralRatio_eq_transitive _ (by omega)]

/-- At every odd order, actual regularity removes switching freedom: precisely
the ordinary carousel isomorphism class maximizes the spectral ratio. -/
theorem regular_spectralRatio_eq_carousel_iff_relabel (m : ℕ)
    (T : Tournament (2 * m + 1)) (hreg : ∀ i, score T i = 0) :
    spectralRatio T = spectralRatio (carouselTournament m) ↔
      ∃ e : Equiv.Perm (Fin (2 * m + 1)), relabelTournament T e = carouselTournament m := by
  rw [carousel_spectralRatio_eq_alternating, spectralRatio_eq_iff_signedPermutationTransitive]
  exact tournament_regular_signedPermutationTransitive_iff_relabel_carousel m T hreg

end TournamentHamiltonian.Equality
