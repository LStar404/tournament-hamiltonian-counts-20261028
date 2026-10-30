module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic

/-!
# The squared-norm consequence of weak majorization

The Fang--Huang comparison uses nonnegative decreasing rearrangements.
This file proves the norm implication from prefix inequalities.  It does
not assert the yet-unproved tournament matrix rearrangement comparison.
-/

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

/-- The Abel-summation criterion for a matrix to preserve prefix domination.
The comparison matrix K_n is a later concrete instance of these column-prefix
conditions; this theorem does not take that instance for granted. -/
theorem matrix_preserves_weak_prefix_of_column_prefix (n : ℕ) (M : ℕ → ℕ → ℝ)
    (u v : ℕ → ℝ)
    (hprefix : ∀ k ≤ n, ∑ i ∈ Finset.range k, u i ≤ ∑ i ∈ Finset.range k, v i)
    (hcol0 : ∀ r ≤ n, ∀ j, 0 ≤ ∑ i ∈ Finset.range r, M i j)
    (hcol : ∀ r ≤ n, AntitoneOn (fun j => ∑ i ∈ Finset.range r, M i j) (Set.Iio n)) :
    ∀ r ≤ n,
      (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range n, M i j * u j) ≤
      (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range n, M i j * v j) := by
  intro r hr
  have h := Finset.sum_mul_le_sum_mul_of_sum_range_le hprefix (hcol0 r hr) (hcol r hr)
  have rearrange (w : ℕ → ℝ) :
      (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range n, M i j * w j) =
      ∑ j ∈ Finset.range n, w j * (∑ i ∈ Finset.range r, M i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [rearrange u, rearrange v]
  exact h

/-- Prefix domination of two decreasing nonnegative vectors controls their
squared Euclidean masses.  A value outside the finite window is irrelevant. -/
theorem sum_sq_le_of_weak_prefix_majorization (n : ℕ) (u v : ℕ → ℝ)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i)
    (hu : AntitoneOn u (Set.Iio n)) (hv : AntitoneOn v (Set.Iio n))
    (hprefix : ∀ k ≤ n, ∑ i ∈ Finset.range k, u i ≤ ∑ i ∈ Finset.range k, v i) :
    ∑ i ∈ Finset.range n, u i ^ 2 ≤ ∑ i ∈ Finset.range n, v i ^ 2 := by
  have h := Finset.sum_mul_le_sum_mul_of_sum_range_le hprefix
    (g := fun i => u i + v i) (fun i => add_nonneg (hu0 i) (hv0 i))
    (fun i hi j hj hij => add_le_add (hu hi hj hij) (hv hi hj hij))
  have huEq : (∑ i ∈ Finset.range n, u i * (u i + v i)) =
      (∑ i ∈ Finset.range n, u i ^ 2) + ∑ i ∈ Finset.range n, u i * v i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hvEq : (∑ i ∈ Finset.range n, v i * (u i + v i)) =
      (∑ i ∈ Finset.range n, v i ^ 2) + ∑ i ∈ Finset.range n, u i * v i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [huEq, hvEq] at h
  linarith

end TournamentHamiltonian
