module

public import TournamentHamiltonian.ComparisonMatrix

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

/-- The integer ceiling of half a square. -/
def halfSquare (h : ℕ) : ℕ := (h * h + 1) / 2

def blockBudget (n r k : ℕ) : ℝ :=
  (r : ℝ) * k - (halfSquare (r + k - n) : ℝ)

@[simp] theorem halfSquare_zero : halfSquare 0 = 0 := by norm_num [halfSquare]

theorem halfSquare_mono : Monotone halfSquare := by
  intro a b hab
  unfold halfSquare
  exact Nat.div_le_div_right (by nlinarith)

theorem halfSquare_le_sum_sq (a b : ℕ) : halfSquare (a + b) ≤ a * a + b * b := by
  have hreal : ((a : ℝ) + b) * (a + b) ≤ 2 * ((a : ℝ) * a + b * b) := by
    nlinarith [sq_nonneg ((a : ℝ) - b)]
  have hnat : (a + b) * (a + b) ≤ 2 * (a * a + b * b) := by exact_mod_cast hreal
  unfold halfSquare
  omega

theorem halfSquare_even (q : ℕ) : halfSquare (2 * q) = 2 * q * q := by
  unfold halfSquare
  have he : 2 * q * (2 * q) + 1 = 2 * (2 * q * q) + 1 := by ring
  rw [he]
  omega

theorem halfSquare_odd (q : ℕ) : halfSquare (2 * q + 1) = 2 * q * q + 2 * q + 1 := by
  unfold halfSquare
  have he : (2 * q + 1) * (2 * q + 1) + 1 = 2 * (2 * q * q + 2 * q + 1) := by ring
  rw [he]
  omega

theorem halfSquare_succ (t : ℕ) :
    halfSquare (t + 1) = halfSquare t + (2 * (t / 2) + 1) := by
  rcases Nat.even_or_odd t with ⟨q, hq⟩ | ⟨q, hq⟩
  · have he : t = 2 * q := by omega
    subst t
    simp only [← two_mul]
    rw [halfSquare_odd, halfSquare_even]
    have hd : 2 * q / 2 = q := by omega
    rw [hd]
    ring
  · have he : t = 2 * q + 1 := by omega
    subst t
    have he' : 2 * q + 1 + 1 = 2 * (q + 1) := by omega
    rw [he', halfSquare_even, halfSquare_odd]
    have hd : (2 * q + 1) / 2 = q := by omega
    rw [hd]
    ring

theorem blockBudget_succ (n r k : ℕ) (hr : r ≤ n) (hk : k < n) :
    blockBudget n r (k + 1) = blockBudget n r k + (comparisonPrefix n r k : ℝ) := by
  by_cases hsmall : r + k + 1 ≤ n
  · have h0 : r + k - n = 0 := by omega
    have h1 : r + (k + 1) - n = 0 := by omega
    simp only [blockBudget, h0, h1, halfSquare_zero, Nat.cast_zero, sub_zero,
      comparisonPrefix, hsmall, ite_true, Nat.cast_add, Nat.cast_one]
    ring
  · have hstep : r + (k + 1) - n = (r + k - n) + 1 := by omega
    have hs : halfSquare (r + (k + 1) - n) =
        halfSquare (r + k - n) + (2 * ((r + k - n) / 2) + 1) := by
      rw [hstep, halfSquare_succ]
    have hp : comparisonPrefix n r k + (2 * ((r + k - n) / 2) + 1) = r := by
      unfold comparisonPrefix
      split_ifs <;> omega
    have hsR : (halfSquare (r + (k + 1) - n) : ℝ) =
        halfSquare (r + k - n) + (2 * ((r + k - n) / 2) + 1 : ℕ) := by
      exact_mod_cast hs
    have hpR : (comparisonPrefix n r k : ℝ) + (2 * ((r + k - n) / 2) + 1 : ℕ) = r := by
      exact_mod_cast hp
    unfold blockBudget
    push_cast
    linarith

/-- The actual comparison matrix column-prefix weights have budget W(r,k). -/
theorem comparisonPrefix_block_sum (n r k : ℕ) (hr : r ≤ n) (hk : k ≤ n) :
    (∑ j ∈ Finset.range k, (comparisonPrefix n r j : ℝ)) = blockBudget n r k := by
  revert hk
  induction k with
  | zero =>
    intro _
    simp [blockBudget, Nat.sub_eq_zero_of_le hr]
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, ih (by omega), blockBudget_succ n r k hr (by omega)]

theorem comparisonKernel_block_sum (n r k : ℕ) (hr : r ≤ n) (hk : k ≤ n) :
    (∑ i ∈ Finset.range r, ∑ j ∈ Finset.range k, comparisonKernel n i j) =
      blockBudget n r k := by
  rw [Finset.sum_comm]
  simp_rw [comparisonKernel_prefix_sum]
  exact comparisonPrefix_block_sum n r k hr hk

end TournamentHamiltonian
