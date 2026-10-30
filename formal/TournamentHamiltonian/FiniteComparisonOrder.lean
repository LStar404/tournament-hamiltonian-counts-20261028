module

public import TournamentHamiltonian.FiniteVectorOrder
public import TournamentHamiltonian.ComparisonBudget

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open scoped Matrix

theorem finComparison_prefix {n : ℕ} (r : ℕ) (hr : r ≤ n) (j : Fin n) :
    finPrefixSum (fun i => comparisonMatrix n i j) r = (comparisonPrefix n r j.val : ℝ) := by
  rw [finPrefixSum_eq_range _ r hr]
  calc
    _ = ∑ i ∈ Finset.range r, comparisonKernel n i j.val := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [extendFinVec, dif_pos ((Finset.mem_range.mp hi).trans_le hr), comparisonMatrix]
    _ = _ := comparisonKernel_prefix_sum n r j.val

theorem finComparison_prefix_mulVec {n : ℕ} (x : Fin n → ℝ) (r : ℕ) (hr : r ≤ n) :
    finPrefixSum (comparisonMatrix n *ᵥ x) r =
      ∑ j, (comparisonPrefix n r j.val : ℝ) * x j := by
  unfold finPrefixSum
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  change finPrefixSum (fun i => comparisonMatrix n i j) r * x j = _
  rw [finComparison_prefix r hr j]

theorem finComparison_prefix_weight_sum {n : ℕ} (r k : ℕ) (hr : r ≤ n) (hk : k ≤ n) :
    finPrefixSum (fun j : Fin n => (comparisonPrefix n r j.val : ℝ)) k = blockBudget n r k := by
  rw [finPrefixSum_eq_range _ k hk]
  calc
    _ = ∑ j ∈ Finset.range k, (comparisonPrefix n r j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [extendFinVec, (Finset.mem_range.mp hj).trans_le hk]
    _ = _ := comparisonPrefix_block_sum n r k hr hk

theorem comparisonMatrix_preserves_finPrefix {n : ℕ} (u v : Fin n → ℝ)
    (h : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r) :
    ∀ r ≤ n, finPrefixSum (comparisonMatrix n *ᵥ u) r ≤
      finPrefixSum (comparisonMatrix n *ᵥ v) r := by
  intro r hr
  rw [finComparison_prefix_mulVec u r hr, finComparison_prefix_mulVec v r hr]
  have hw0 : ∀ j : Fin n, 0 ≤ (comparisonPrefix n r j.val : ℝ) := fun _ => Nat.cast_nonneg _
  have hw : Antitone (fun j : Fin n => (comparisonPrefix n r j.val : ℝ)) := by
    intro i j hij
    change (comparisonPrefix n r j.val : ℝ) ≤ (comparisonPrefix n r i.val : ℝ)
    exact Nat.cast_le.mpr (comparisonPrefix_antitone n r hij)
  have hd := finite_dot_le_of_prefix_le u v (fun j => (comparisonPrefix n r j.val : ℝ)) hw0 hw h
  simpa only [mul_comm] using hd

theorem finComparison_mulVec_eq_comparisonMul {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (comparisonMatrix n *ᵥ x) i = comparisonMul n (extendFinVec x) i.val := by
  simp only [Matrix.mulVec, dotProduct, comparisonMul]
  rw [sum_fin_eq_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp [extendFinVec, Finset.mem_range.mp hj, comparisonMatrix]

theorem comparisonMatrix_preserves_decreasingNonneg {n : ℕ} {x : Fin n → ℝ}
    (hx : DecreasingNonneg x) : DecreasingNonneg (comparisonMatrix n *ᵥ x) := by
  have h0 := extendFinVec_nonneg hx.1
  have ha := extendFinVec_antitone hx.2
  constructor
  · intro i
    rw [finComparison_mulVec_eq_comparisonMul]
    exact comparisonMul_nonneg n _ h0 ha i.val i.isLt
  · intro i j hij
    rw [finComparison_mulVec_eq_comparisonMul, finComparison_mulVec_eq_comparisonMul]
    exact comparisonMul_antitone n _ h0 ha i.isLt j.isLt hij

end TournamentHamiltonian
