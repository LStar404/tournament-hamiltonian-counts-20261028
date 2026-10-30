module

public import TournamentHamiltonian.Equality.KPrefixEquality
public import TournamentHamiltonian.FrobeniusComparison

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open scoped BigOperators Matrix

/-- Equality at one step of the comparison chain determines the sorted
absolute input, not merely its norm. -/
theorem sorted_abs_eq_of_mulVec_comparison_sq_eq {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) (hentry : ∀ i j, |A i j| ≤ 1)
    (x y : Fin n → ℝ) (hxy : AbsDom x y)
    (heq : (∑ i, (A *ᵥ x) i ^ 2) = ∑ i, (comparisonMatrix n *ᵥ y) i ^ 2) :
    ∃ π : Equiv.Perm (Fin n), (fun i => |x (π i)|) = y := by
  obtain ⟨π, ha⟩ := sorted_abs_exists x
  have hp : ∀ r ≤ n, finPrefixSum (fun i => |x (π i)|) r ≤ finPrefixSum y r :=
    fun r hr => absDom_sorted_prefix hxy π r hr
  have h₁ := sum_sq_le_of_absDom (absDom_mulVec_comparison_sorted A hskew hentry x π ha)
  have h₂ := finite_sum_sq_le_of_prefix_le _ _
    (comparisonMatrix_preserves_decreasingNonneg ha)
    (comparisonMatrix_preserves_finPrefix _ y hp)
  have hsame : (∑ i, (comparisonMatrix n *ᵥ (fun j => |x (π j)|)) i ^ 2) =
      ∑ i, (comparisonMatrix n *ᵥ y) i ^ 2 := by linarith
  exact ⟨π, eq_of_comparison_sq_sum_eq_of_finPrefix_le hn _ y ha hp hsame⟩

/-- A saturated comparison after one A-step forces equality of the preceding
input square sums. This is the local backward propagation of equality. -/
theorem sq_sum_eq_of_mulVec_comparison_sq_eq {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) (hentry : ∀ i j, |A i j| ≤ 1)
    (x y : Fin n → ℝ) (hxy : AbsDom x y)
    (heq : (∑ i, (A *ᵥ x) i ^ 2) = ∑ i, (comparisonMatrix n *ᵥ y) i ^ 2) :
    (∑ i, x i ^ 2) = ∑ i, y i ^ 2 := by
  obtain ⟨π, hπ⟩ := sorted_abs_eq_of_mulVec_comparison_sq_eq hn A hskew hentry x y hxy heq
  calc
    _ = ∑ i, |x (π i)| ^ 2 := by
      symm
      apply Fintype.sum_equiv π
      intro i
      exact sq_abs (x (π i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [congrFun hπ i]

/-- Equality in one column at power p+1 propagates to power p. -/
theorem skew_pow_column_sq_eq_of_succ_eq {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : A.transpose = -A) (hentry : ∀ i j, |A i j| ≤ 1)
    (p : ℕ) (j : Fin n)
    (heq : (∑ i, ((A ^ (p + 1)) i j) ^ 2) =
      ∑ i, (((comparisonMatrix n) ^ (p + 1)) i ⟨0, by omega⟩) ^ 2) :
    (∑ i, ((A ^ p) i j) ^ 2) =
      ∑ i, (((comparisonMatrix n) ^ p) i ⟨0, by omega⟩) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hp : ∀ i j, A i j = -A j i := by
    intro i j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using congrFun (congrFun hskew j) i
  have hxy := skew_pow_basis_absDom A hn0 hp hentry p j
  have heq' : (∑ i, (A *ᵥ ((A ^ p) *ᵥ finiteBasisVector j)) i ^ 2) =
      ∑ i, (comparisonMatrix n *ᵥ
        (((comparisonMatrix n) ^ p) *ᵥ finiteBasisVector ⟨0, hn0⟩)) i ^ 2 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_succ', ← pow_succ']
    simpa only [Matrix.mulVec, dotProduct,
      finiteBasisVector, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using heq
  have h := sq_sum_eq_of_mulVec_comparison_sq_eq hn A hp hentry _ _ hxy heq'
  simpa only [Matrix.mulVec, dotProduct, finiteBasisVector, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

/-- Saturation of the Frobenius bound forces every bounded column to saturate. -/
theorem skew_pow_column_sq_eq_of_frob_eq {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : A.transpose = -A) (hentry : ∀ i j, |A i j| ≤ 1) (p : ℕ)
    (heq : matrixFrobSq (A ^ p) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ p)) (j : Fin n) :
    (∑ i, ((A ^ p) i j) ^ 2) =
      ∑ i, (((comparisonMatrix n) ^ p) i ⟨0, hn⟩) ^ 2 := by
  have hs : (∑ j, ∑ i, ((A ^ p) i j) ^ 2) =
      ∑ _j : Fin n, ∑ i, (((comparisonMatrix n) ^ p) i ⟨0, hn⟩) ^ 2 := by
    calc
      _ = matrixFrobSq (A ^ p) := Finset.sum_comm
      _ = matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ p) := heq
      _ = (n : ℝ) * (∑ i, (((comparisonMatrix n) ^ p) i ⟨0, hn⟩) ^ 2) := by
        rw [transitive_frob_pow_eq_card_mul_diag n hn p,
          comparison_pow_first_column_sq_eq_transitive_gram n hn p]
      _ = _ := by simp
  exact (Finset.sum_eq_sum_iff_of_le (fun j _ =>
    skew_pow_column_sq_le_comparison A hn hskew hentry p j)).mp hs j (Finset.mem_univ j)

/-- Frobenius equality at exponent p+1 propagates to exponent p, for n >= 2. -/
theorem skew_frob_eq_of_succ_eq {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : A.transpose = -A) (hentry : ∀ i j, |A i j| ≤ 1) (p : ℕ)
    (heq : matrixFrobSq (A ^ (p + 1)) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ (p + 1))) :
    matrixFrobSq (A ^ p) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ p) := by
  have hn0 : 0 < n := by omega
  have hc (j : Fin n) := skew_pow_column_sq_eq_of_succ_eq hn A hskew hentry p j
    (skew_pow_column_sq_eq_of_frob_eq hn0 A hskew hentry (p + 1) heq j)
  calc
    _ = ∑ j, ∑ i, ((A ^ p) i j) ^ 2 := Finset.sum_comm
    _ = ∑ _j : Fin n, ∑ i, (((comparisonMatrix n) ^ p) i ⟨0, hn0⟩) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      exact hc j
    _ = (n : ℝ) * (∑ i, (((comparisonMatrix n) ^ p) i ⟨0, hn0⟩) ^ 2) := by simp
    _ = _ := by
      rw [transitive_frob_pow_eq_card_mul_diag n hn0 p,
        comparison_pow_first_column_sq_eq_transitive_gram n hn0 p]

/-- Equality at a higher exponent forces equality at every smaller exponent. -/
theorem skew_frob_eq_of_le_of_eq {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : A.transpose = -A) (hentry : ∀ i j, |A i j| ≤ 1)
    (p q : ℕ) (hqp : q ≤ p)
    (heq : matrixFrobSq (A ^ p) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ p)) :
    matrixFrobSq (A ^ q) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ q) := by
  induction p generalizing q with
  | zero =>
    have hq : q = 0 := by omega
    simpa [hq] using heq
  | succ p ih =>
    by_cases hq : q = p + 1
    · simpa [hq] using heq
    · exact ih q (by omega) (skew_frob_eq_of_succ_eq hn A hskew hentry p heq)

/-- Any strict Frobenius comparison propagates to every higher exponent. -/
theorem skew_frob_lt_of_le_of_lt {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : A.transpose = -A) (hentry : ∀ i j, |A i j| ≤ 1)
    (p q : ℕ) (hqp : q ≤ p)
    (hlt : matrixFrobSq (A ^ q) <
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ q)) :
    matrixFrobSq (A ^ p) <
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ p) := by
  have hle := skew_pow_frob_le_transitive A (by omega) hskew hentry p
  rcases lt_or_eq_of_le hle with hlt' | heq
  · exact hlt'
  · have heq' := skew_frob_eq_of_le_of_eq hn A hskew hentry p q hqp heq
    exact False.elim ((ne_of_lt hlt) heq')

end TournamentHamiltonian
