module

public import TournamentHamiltonian.Equality.SpectralClassification

@[expose] public section

set_option autoImplicit false

namespace TournamentHamiltonian.Equality

open scoped Matrix

/-- A fixed, tie-safe permutation that sorts actual coordinate absolute values. -/
noncomputable def absSortingPerm {n : ℕ} (x : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => -|x i|)

/-- The manuscript's `x*`, with all multiplicities and zero coordinates retained. -/
noncomputable def sortedAbs {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => |x (absSortingPerm x i)|

theorem sortedAbs_decreasingNonneg {n : ℕ} (x : Fin n → ℝ) :
    DecreasingNonneg (sortedAbs x) := by
  refine ⟨fun _ => abs_nonneg _, ?_⟩
  intro i j hij
  have h := Tuple.monotone_sort (fun i => -|x i|) hij
  change -sortedAbs x i ≤ -sortedAbs x j at h
  linarith

theorem sortedAbs_sum_sq {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, sortedAbs x i ^ 2) = ∑ i, x i ^ 2 := by
  apply Fintype.sum_equiv (absSortingPerm x)
  intro i
  exact sq_abs (x (absSortingPerm x i))

@[simp] theorem sortedAbs_zero (n : ℕ) : sortedAbs (0 : Fin n → ℝ) = 0 := by
  ext i
  simp [sortedAbs]

theorem sortedAbs_prefix_le_of_absDom {n : ℕ} {x y : Fin n → ℝ} (h : AbsDom x y)
    (r : ℕ) (hr : r ≤ n) : finPrefixSum (sortedAbs x) r ≤ finPrefixSum y r :=
  absDom_sorted_prefix h (absSortingPerm x) r hr

theorem IsSkewSign.entry_abs_le_one {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSkewSign A) (i j : Fin n) : |A i j| ≤ 1 := by
  by_cases hij : i = j
  · subst j; simp [hA.diag]
  · rcases hA.signs i j hij with h | h <;> simp [h]

theorem comparison_power_sortedAbs_decreasingNonneg {n : ℕ}
    (p : ℕ) (x : Fin n → ℝ) :
    DecreasingNonneg ((comparisonMatrix n ^ p) *ᵥ sortedAbs x) := by
  induction p with
  | zero => simpa using sortedAbs_decreasingNonneg x
  | succ p ih =>
    simpa only [pow_succ', Matrix.mulVec_mulVec] using
      comparisonMatrix_preserves_decreasingNonneg ih

/-- Arbitrary products of potentially different actual skew sign matrices.
No repeated-matrix or common-eigenbasis assumption is used. -/
theorem skew_sign_list_product_sortedAbs_prefix {n : ℕ}
    (As : List (Matrix (Fin n) (Fin n) ℝ))
    (hAs : ∀ A ∈ As, IsSkewSign A) (x : Fin n → ℝ) :
    ∀ r ≤ n, finPrefixSum (sortedAbs (As.prod *ᵥ x)) r ≤
      finPrefixSum ((comparisonMatrix n ^ As.length) *ᵥ sortedAbs x) r := by
  induction As with
  | nil => simp
  | cons A As ih =>
    have hA := hAs A (by simp)
    have ht : ∀ B ∈ As, IsSkewSign B := fun B hB => hAs B (by simp [hB])
    intro r hr
    have hs := sortedAbs_prefix_le_of_absDom
      (absDom_mulVec_comparison_sorted A hA.skew hA.entry_abs_le_one
        (As.prod *ᵥ x) (absSortingPerm _) (sortedAbs_decreasingNonneg _)) r hr
    have hp := comparisonMatrix_preserves_finPrefix
      (sortedAbs (As.prod *ᵥ x)) ((comparisonMatrix n ^ As.length) *ᵥ sortedAbs x)
      (ih ht) r hr
    simpa only [List.prod_cons, Matrix.mulVec_mulVec, List.length_cons, pow_succ'] using hs.trans hp

/-- One saturated outer comparison forces saturation of the preceding suffix,
using injectivity of K only along the comparable prefix pair. -/
theorem sortedAbs_tail_eq_of_cons_eq {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (As : List (Matrix (Fin n) (Fin n) ℝ))
    (hA : IsSkewSign A) (hAs : ∀ B ∈ As, IsSkewSign B) (x : Fin n → ℝ)
    (heq : sortedAbs ((A :: As).prod *ᵥ x) =
      (comparisonMatrix n ^ (A :: As).length) *ᵥ sortedAbs x) :
    sortedAbs (As.prod *ᵥ x) = (comparisonMatrix n ^ As.length) *ᵥ sortedAbs x := by
  have hp := skew_sign_list_product_sortedAbs_prefix As hAs x
  have h₁ := sum_sq_le_of_absDom
    (absDom_mulVec_comparison_sorted A hA.skew hA.entry_abs_le_one
      (As.prod *ᵥ x) (absSortingPerm _) (sortedAbs_decreasingNonneg _))
  have h₂ := finite_sum_sq_le_of_prefix_le _ _
    (comparisonMatrix_preserves_decreasingNonneg (sortedAbs_decreasingNonneg (As.prod *ᵥ x)))
    (comparisonMatrix_preserves_finPrefix _ _ hp)
  have heqsq := congrArg (fun v : Fin n → ℝ => ∑ i, v i ^ 2) heq
  rw [sortedAbs_sum_sq] at heqsq
  simp only [List.prod_cons, List.length_cons] at heqsq
  rw [pow_succ' (comparisonMatrix n) As.length] at heqsq
  simp only [← Matrix.mulVec_mulVec] at heqsq
  apply eq_of_comparison_sq_sum_eq_of_finPrefix_le hn _ _ (sortedAbs_decreasingNonneg _) hp
  change (∑ i, (A *ᵥ (As.prod *ᵥ x)) i ^ 2) ≤
    ∑ i, (comparisonMatrix n *ᵥ sortedAbs (As.prod *ᵥ x)) i ^ 2 at h₁
  linarith

/-- In dimensions zero or one every skew matrix and the comparison matrix vanish. -/
theorem skew_sign_matrix_eq_zero_of_small_dimension {n : ℕ} (hn : n ≤ 1)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSkewSign A) : A = 0 := by
  ext i j
  have hij : i = j := Fin.ext (by omega)
  subst j
  exact hA.diag i

theorem comparisonMatrix_eq_zero_of_small_dimension {n : ℕ} (hn : n ≤ 1) :
    comparisonMatrix n = 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · ext i; exact Fin.elim0 i
  · ext i j
    fin_cases i; fin_cases j
    norm_num [comparisonMatrix, comparisonKernel, comparisonPrefix]

/-- Small dimensions are handled directly, without using the false assertion
that K_1 is injective. Every suffix comparison already is an equality. -/
theorem skew_sign_list_product_sortedAbs_eq_small_dimension {n : ℕ} (hn : n ≤ 1)
    (As : List (Matrix (Fin n) (Fin n) ℝ))
    (hAs : ∀ A ∈ As, IsSkewSign A) (x : Fin n → ℝ) :
    sortedAbs (As.prod *ᵥ x) = (comparisonMatrix n ^ As.length) *ᵥ sortedAbs x := by
  cases As with
  | nil => simp
  | cons A As =>
    have hA := skew_sign_matrix_eq_zero_of_small_dimension hn (hAs A (by simp))
    simp [List.prod_cons, hA, comparisonMatrix_eq_zero_of_small_dimension hn]

/-- Equality of vectors in the outermost comparison forces equality for every
suffix product, including the empty suffix; dimensions 0 and 1 are included. -/
theorem skew_sign_list_product_sortedAbs_eq_all_suffixes {n : ℕ}
    (As : List (Matrix (Fin n) (Fin n) ℝ))
    (hAs : ∀ A ∈ As, IsSkewSign A) (x : Fin n → ℝ)
    (heq : sortedAbs (As.prod *ᵥ x) =
      (comparisonMatrix n ^ As.length) *ᵥ sortedAbs x) :
    ∀ k : ℕ, sortedAbs ((As.drop k).prod *ᵥ x) =
      (comparisonMatrix n ^ (As.drop k).length) *ᵥ sortedAbs x := by
  by_cases hn : 2 ≤ n
  · induction As with
    | nil => simp
    | cons A As ih =>
      have hA := hAs A (by simp)
      have ht : ∀ B ∈ As, IsSkewSign B := fun B hB => hAs B (by simp [hB])
      intro k
      cases k with
      | zero => simpa using heq
      | succ k =>
        simpa only [List.drop_succ_cons] using
          ih ht (sortedAbs_tail_eq_of_cons_eq hn A As hA ht x heq) k
  · intro k
    apply skew_sign_list_product_sortedAbs_eq_small_dimension (by omega) (As.drop k)
    intro A hA
    exact hAs A (List.mem_of_mem_drop hA)

/-- Literal theorem 6.2 for a list of genuine tournaments, with the original
right-hand side nonnegative decreasing and the original suffix equality. -/
theorem tournament_list_product_comparison_and_suffixes {n : ℕ}
    (Ts : List (Tournament n)) (x : Fin n → ℝ) :
    DecreasingNonneg ((comparisonMatrix n ^ Ts.length) *ᵥ sortedAbs x) ∧
    (∀ r ≤ n, finPrefixSum (sortedAbs ((Ts.map signMatrix).prod *ᵥ x)) r ≤
      finPrefixSum ((comparisonMatrix n ^ Ts.length) *ᵥ sortedAbs x) r) ∧
    (sortedAbs ((Ts.map signMatrix).prod *ᵥ x) =
        (comparisonMatrix n ^ Ts.length) *ᵥ sortedAbs x →
      ∀ k : ℕ, sortedAbs (((Ts.drop k).map signMatrix).prod *ᵥ x) =
        (comparisonMatrix n ^ (Ts.drop k).length) *ᵥ sortedAbs x) := by
  have hAs : ∀ A ∈ Ts.map signMatrix, IsSkewSign A := by
    intro A hA
    obtain ⟨T, _, rfl⟩ := List.mem_map.mp hA
    exact signMatrix_isSkewSign T
  refine ⟨comparison_power_sortedAbs_decreasingNonneg _ _, ?_, ?_⟩
  · simpa only [List.length_map] using skew_sign_list_product_sortedAbs_prefix (Ts.map signMatrix) hAs x
  · intro heq k
    have h := skew_sign_list_product_sortedAbs_eq_all_suffixes (Ts.map signMatrix) hAs x
      (by simpa only [List.length_map] using heq) k
    simpa only [← List.map_drop, List.length_map] using h

end TournamentHamiltonian.Equality
