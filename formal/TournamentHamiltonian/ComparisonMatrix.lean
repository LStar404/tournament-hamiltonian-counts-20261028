module

public import TournamentHamiltonian.WeakMajorization
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Algebra.Ring.Parity

/-!
# Prefix construction of the Fang--Huang comparison operator

The column prefix is encoded directly as a natural number. Its first
`n-r` values equal r, followed by r-1,r-1,r-3,r-3,... . Discrete differences
recover the comparison operator and make its prefix-monotonicity exact.
The entries are identified with the usual alternating sign formula below.
The one-step comparison for arbitrary tournament matrices remains separate.
-/

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

def comparisonPrefix (n r j : ℕ) : ℕ :=
  if r + j + 1 ≤ n then r else r + 1 - 2 * ((r + j + 2 - n) / 2)

theorem comparisonPrefix_zero (n j : ℕ) : comparisonPrefix n 0 j = 0 := by
  unfold comparisonPrefix
  split_ifs <;> omega

theorem comparisonPrefix_antitone (n r : ℕ) : Antitone (comparisonPrefix n r) := by
  intro i j hij
  unfold comparisonPrefix
  split_ifs <;> omega

/-- Discrete differences in row-prefix length, before restricting to Fin n. -/
def comparisonKernel (n i j : ℕ) : ℝ :=
  (comparisonPrefix n (i + 1) j : ℝ) - comparisonPrefix n i j

def comparisonMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => comparisonKernel n i.val j.val

theorem comparisonKernel_prefix_sum (n r j : ℕ) :
    (∑ i ∈ Finset.range r, comparisonKernel n i j) = comparisonPrefix n r j := by
  induction r with
  | zero => simp [comparisonPrefix_zero]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    unfold comparisonKernel
    ring

theorem comparisonKernel_above_antidiagonal (n i j : ℕ) (h : i + j + 1 < n) :
    comparisonKernel n i j = 1 := by
  unfold comparisonKernel comparisonPrefix
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  push_cast
  ring

theorem comparisonKernel_antidiagonal (n i j : ℕ) (h : i + j + 1 = n) :
    comparisonKernel n i j = 0 := by
  have hprev : comparisonPrefix n i j = i := by
    unfold comparisonPrefix
    split_ifs <;> omega
  have hnext : comparisonPrefix n (i + 1) j = i := by
    unfold comparisonPrefix
    split_ifs <;> omega
  simp [comparisonKernel, hprev, hnext]

theorem comparisonKernel_below_antidiagonal (n i j : ℕ)
    (hi : i < n) (hj : j < n) (h : n < i + j + 1) :
    comparisonKernel n i j = (-1 : ℝ) ^ (i + j - n) := by
  simp only [neg_one_pow_eq_ite, Nat.even_iff]
  split_ifs with heven
  · have hp : comparisonPrefix n (i + 1) j = comparisonPrefix n i j + 1 := by
      unfold comparisonPrefix
      split_ifs <;> omega
    simp only [comparisonKernel, hp, Nat.cast_add, Nat.cast_one]
    ring
  · have hp : comparisonPrefix n (i + 1) j + 1 = comparisonPrefix n i j := by
      unfold comparisonPrefix
      split_ifs <;> omega
    have hc : (comparisonPrefix n (i + 1) j : ℝ) + 1 = comparisonPrefix n i j := by
      exact_mod_cast hp
    unfold comparisonKernel
    linarith

/-- Entrywise identification with the usual all-order Fang--Huang matrix. -/
theorem comparisonMatrix_apply (n : ℕ) (i j : Fin n) :
    comparisonMatrix n i j =
      if i.val + j.val + 1 < n then 1 else
      if i.val + j.val + 1 = n then 0 else (-1 : ℝ) ^ (i.val + j.val - n) := by
  by_cases hlt : i.val + j.val + 1 < n
  · simp [comparisonMatrix, hlt, comparisonKernel_above_antidiagonal n i.val j.val hlt]
  · by_cases heq : i.val + j.val + 1 = n
    · simp [comparisonMatrix, hlt, heq, comparisonKernel_antidiagonal n i.val j.val heq]
    · simp [comparisonMatrix, hlt, heq,
        comparisonKernel_below_antidiagonal n i.val j.val i.isLt j.isLt (by omega)]

theorem comparisonMatrix_symmetric (n : ℕ) :
    (comparisonMatrix n).transpose = comparisonMatrix n := by
  ext i j
  simp only [Matrix.transpose_apply, comparisonMatrix_apply]
  simp [Nat.add_comm]

theorem comparisonKernel_symmetric (n i j : ℕ) (hi : i < n) (hj : j < n) :
    comparisonKernel n i j = comparisonKernel n j i := by
  have h := congrFun (congrFun (comparisonMatrix_symmetric n) ⟨j, hj⟩) ⟨i, hi⟩
  exact h

theorem comparisonKernel_row_prefix_sum (n i r : ℕ) (hi : i < n) (hr : r ≤ n) :
    (∑ j ∈ Finset.range r, comparisonKernel n i j) = comparisonPrefix n r i := by
  calc
    _ = ∑ j ∈ Finset.range r, comparisonKernel n j i := by
      apply Finset.sum_congr rfl
      intro j hj
      exact comparisonKernel_symmetric n i j hi ((Finset.mem_range.mp hj).trans_le hr)
    _ = _ := comparisonKernel_prefix_sum n r i

def comparisonMul (n : ℕ) (u : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, comparisonKernel n i j * u j

/-- Nonnegative decreasing inputs remain nonnegative on the finite window. -/
theorem comparisonMul_nonneg (n : ℕ) (u : ℕ → ℝ)
    (hu0 : ∀ j, 0 ≤ u j) (hu : AntitoneOn u (Set.Iio n))
    (i : ℕ) (hi : i < n) : 0 ≤ comparisonMul n u i := by
  have hp : ∀ r ≤ n, (∑ j ∈ Finset.range r, (0 : ℝ)) ≤
      ∑ j ∈ Finset.range r, comparisonKernel n i j := by
    intro r hr
    rw [comparisonKernel_row_prefix_sum n i r hi hr]
    simp
  have h := Finset.sum_mul_le_sum_mul_of_sum_range_le hp hu0 hu
  simpa only [zero_mul, Finset.sum_const_zero, comparisonMul] using h

/-- The comparison operator also preserves the decreasing order. -/
theorem comparisonMul_antitone (n : ℕ) (u : ℕ → ℝ)
    (hu0 : ∀ j, 0 ≤ u j) (hu : AntitoneOn u (Set.Iio n)) :
    AntitoneOn (comparisonMul n u) (Set.Iio n) := by
  intro i hi j hj hij
  have hp : ∀ r ≤ n, (∑ k ∈ Finset.range r, comparisonKernel n j k) ≤
      ∑ k ∈ Finset.range r, comparisonKernel n i k := by
    intro r hr
    rw [comparisonKernel_row_prefix_sum n j r hj hr,
      comparisonKernel_row_prefix_sum n i r hi hr]
    exact_mod_cast comparisonPrefix_antitone n r hij
  exact Finset.sum_mul_le_sum_mul_of_sum_range_le hp hu0 hu

/-- The actual comparison operator preserves weak prefix domination at every order. -/
theorem comparisonKernel_preserves_weak_prefix (n : ℕ) (u v : ℕ → ℝ)
    (hprefix : ∀ k ≤ n, ∑ i ∈ Finset.range k, u i ≤ ∑ i ∈ Finset.range k, v i) :
    ∀ r ≤ n,
      (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range n, comparisonKernel n i j * u j) ≤
      (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range n, comparisonKernel n i j * v j) := by
  apply matrix_preserves_weak_prefix_of_column_prefix n (comparisonKernel n) u v hprefix
  · intro r _ j
    rw [comparisonKernel_prefix_sum]
    exact Nat.cast_nonneg _
  · intro r _ i _ j _ hij
    change (∑ k ∈ Finset.range r, comparisonKernel n k j) ≤
      ∑ k ∈ Finset.range r, comparisonKernel n k i
    rw [comparisonKernel_prefix_sum, comparisonKernel_prefix_sum]
    exact_mod_cast comparisonPrefix_antitone n r hij

end TournamentHamiltonian
