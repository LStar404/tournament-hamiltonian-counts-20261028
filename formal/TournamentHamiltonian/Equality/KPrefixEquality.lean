module

public import TournamentHamiltonian.Equality.PrefixEquality
public import TournamentHamiltonian.FiniteComparisonOrder

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open scoped BigOperators Matrix

/-- Equality of all finite prefixes determines the vector, including order zero. -/
theorem eq_of_finPrefixSum_eq {n : ℕ} (u v : Fin n → ℝ)
    (h : ∀ r ≤ n, finPrefixSum u r = finPrefixSum v r) : u = v := by
  funext i
  have h₀ := h i.val (Nat.le_of_lt i.isLt)
  have h₁ := h (i.val + 1) (Nat.succ_le_of_lt i.isLt)
  rw [finPrefixSum_eq_range u i.val (Nat.le_of_lt i.isLt),
    finPrefixSum_eq_range v i.val (Nat.le_of_lt i.isLt)] at h₀
  rw [finPrefixSum_eq_range u (i.val + 1) (Nat.succ_le_of_lt i.isLt),
    finPrefixSum_eq_range v (i.val + 1) (Nat.succ_le_of_lt i.isLt),
    Finset.sum_range_succ, Finset.sum_range_succ] at h₁
  have hu : extendFinVec u i.val = u i := by simp [extendFinVec, i.isLt]
  have hv : extendFinVec v i.val = v i := by simp [extendFinVec, i.isLt]
  rw [hu, hv] at h₁
  linarith

/-- K's column-prefix weight at row length n-k has a unit drop after its
first k entries. Removing that unit step leaves a nonnegative decreasing
weight, so equality after K forces equality in the original kth prefix. -/
theorem finPrefix_eq_of_comparison_mulVec_eq {n : ℕ} (u v : Fin n → ℝ)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r)
    (hK : comparisonMatrix n *ᵥ u = comparisonMatrix n *ᵥ v)
    (k : ℕ) (hk : k < n) : finPrefixSum u k = finPrefixSum v k := by
  let w : Fin n → ℝ := fun j =>
    if j.val < k then ((n - k - 1 : ℕ) : ℝ)
    else (comparisonPrefix n (n - k) j.val : ℝ)
  have hw0 : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    split_ifs <;> exact Nat.cast_nonneg _
  have hw : Antitone w := by
    intro i j hij
    by_cases hi : i.val < k <;> by_cases hj : j.val < k
    · simp [w, hi, hj]
    · have hb : comparisonPrefix n (n - k) j.val ≤ n - k - 1 := by
        unfold comparisonPrefix
        split_ifs <;> omega
      simpa [w, hi, hj] using (Nat.cast_le (α := ℝ)).mpr hb
    · have hij' : i.val ≤ j.val := hij
      omega
    · simpa [w, hi, hj] using (Nat.cast_le (α := ℝ)).mpr
        (comparisonPrefix_antitone n (n - k) (show i.val ≤ j.val from hij))
  have hsplit (j : Fin n) : (comparisonPrefix n (n - k) j.val : ℝ) =
      w j + if j.val < k then 1 else 0 := by
    by_cases hj : j.val < k
    · have hp : comparisonPrefix n (n - k) j.val = n - k := by
        unfold comparisonPrefix
        rw [ite_eq_left (by omega)]
      have hn : n - k = (n - k - 1) + 1 := by omega
      simp only [hp, w, hj, ite_true]
      exact_mod_cast hn
    · simp [w, hj]
  have hdecomp (x : Fin n → ℝ) :
      finPrefixSum (comparisonMatrix n *ᵥ x) (n - k) =
        (∑ j, x j * w j) + finPrefixSum x k := by
    rw [finComparison_prefix_mulVec x (n - k) (Nat.sub_le _ _)]
    calc
      _ = ∑ j, (x j * w j + if j.val < k then x j else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hsplit]
        split_ifs <;> ring
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp [finPrefixSum, finPrefix, Finset.sum_filter]
  have hd := finite_dot_le_of_prefix_le u v w hw0 hw hprefix
  have he := congrArg (fun x => finPrefixSum x (n - k)) hK
  rw [hdecomp u, hdecomp v] at he
  have hp := hprefix k (Nat.le_of_lt hk)
  linarith

/-- The second K-prefix is the total input sum plus its (n-2)nd prefix. -/
theorem finComparison_second_prefix {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    finPrefixSum (comparisonMatrix n *ᵥ x) 2 =
      finPrefixSum x n + finPrefixSum x (n - 2) := by
  have hw (j : Fin n) : comparisonPrefix n 2 j.val =
      if j.val < n - 2 then 2 else 1 := by
    unfold comparisonPrefix
    split_ifs <;> omega
  rw [finComparison_prefix_mulVec x 2 hn]
  calc
    _ = ∑ j, (x j + if j.val < n - 2 then x j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hw]
      split_ifs <;> norm_num <;> ring
    _ = _ := by
      rw [Finset.sum_add_distrib, finPrefixSum_full]
      simp [finPrefixSum, finPrefix, Finset.sum_filter]

/-- K need not be injective in odd order. It is nevertheless injective on
pairs comparable in the weak-prefix order as soon as n >= 2. No monotonicity
or sign assumptions on u and v are needed for this implication. -/
theorem eq_of_comparison_mulVec_eq_of_finPrefix_le {n : ℕ} (hn : 2 ≤ n)
    (u v : Fin n → ℝ)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r)
    (hK : comparisonMatrix n *ᵥ u = comparisonMatrix n *ᵥ v) : u = v := by
  have hp := finPrefix_eq_of_comparison_mulVec_eq u v hprefix hK
  have hlast : finPrefixSum u n = finPrefixSum v n := by
    have h₂ := congrArg (fun x => finPrefixSum x 2) hK
    rw [finComparison_second_prefix hn u, finComparison_second_prefix hn v] at h₂
    have hm := hp (n - 2) (by omega)
    linarith
  apply eq_of_finPrefixSum_eq u v
  intro r hr
  rcases lt_or_eq_of_le hr with hlt | heq
  · exact hp r hlt
  · simpa [heq] using hlast

/-- Equality of square sums after K is rigid along the weak-prefix order.
Only the lower vector u must be decreasing and nonnegative. -/
theorem eq_of_comparison_sq_sum_eq_of_finPrefix_le {n : ℕ} (hn : 2 ≤ n)
    (u v : Fin n → ℝ) (hu : DecreasingNonneg u)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r)
    (hsq : (∑ i, (comparisonMatrix n *ᵥ u) i ^ 2) =
      ∑ i, (comparisonMatrix n *ᵥ v) i ^ 2) : u = v := by
  apply eq_of_comparison_mulVec_eq_of_finPrefix_le hn u v hprefix
  exact eq_of_finPrefix_le_of_sq_sum_eq _ _
    (comparisonMatrix_preserves_decreasingNonneg hu)
    (comparisonMatrix_preserves_finPrefix u v hprefix) hsq

/-- Strict square-sum growth after K for distinct prefix-comparable inputs. -/
theorem comparison_sq_sum_lt_of_finPrefix_le_of_ne {n : ℕ} (hn : 2 ≤ n)
    (u v : Fin n → ℝ) (hu : DecreasingNonneg u)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r) (hne : u ≠ v) :
    (∑ i, (comparisonMatrix n *ᵥ u) i ^ 2) <
      ∑ i, (comparisonMatrix n *ᵥ v) i ^ 2 := by
  have hle := finite_sum_sq_le_of_prefix_le _ _
    (comparisonMatrix_preserves_decreasingNonneg hu)
    (comparisonMatrix_preserves_finPrefix u v hprefix)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact False.elim (hne (eq_of_comparison_sq_sum_eq_of_finPrefix_le hn u v hu hprefix heq))

end TournamentHamiltonian
