module

public import TournamentHamiltonian.UniformBlowup.PathConstraints

@[expose] public section

namespace UniformBlowup
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Deterministic expected adjacency weight: zero on the diagonal, one half
inside a block, and the base adjacency between different blocks. -/
def weight {d m : ℕ} (T : Tournament d) (u v : Vertex d m) : ℝ :=
  if u = v then 0 else if u.1 = v.1 then 1/2 else if T.val u.1 v.1 then 1 else 0

def pathWeight {d m : ℕ} (T : Tournament d) (π : Arrangement d m) : ℝ :=
  ∏ r : Step (d*m), weight T (tail π r) (head π r)

def weightedPathSum {d m : ℕ} (T : Tournament d) : ℝ :=
  ∑ π : Arrangement d m, pathWeight T π

/-- All vertex orderings satisfying actual arcs, with neither reversal nor
starting-point division. -/
def pathCount {d m : ℕ} (T : Tournament d) (ω : Sample d m) : ℕ :=
  (Finset.univ.filter (IsPath T ω)).card

/-- Equal-weight finite expectation on exactly the Boolean orientation cube. -/
def avgPath {d m : ℕ} (T : Tournament d) : ℝ :=
  (∑ ω : Sample d m, (pathCount T ω : ℝ)) / Fintype.card (Sample d m)

theorem pathWeight_eq {d m : ℕ} (T : Tournament d) (π : Arrangement d m) :
    pathWeight T π = if Compatible T π then (1/2 : ℝ) ^ b π else 0 := by
  classical
  by_cases hc : Compatible T π
  · rw [ite_eq_left hc]
    have hf : ∀ r : Step (d*m), weight T (tail π r) (head π r) =
        if (tail π r).1 = (head π r).1 then (1/2 : ℝ) else 1 := by
      intro r
      simp only [weight, ite_eq_right (tail_ne_head π r)]
      by_cases hr : (tail π r).1 = (head π r).1
      · simp [hr]
      · simp [hr, hc r hr]
    simp only [pathWeight, hf]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    congr 1
    rw [b_eq_card_internalStep, Fintype.card_subtype]
  · rw [ite_eq_right hc]
    obtain ⟨r, hr, ha⟩ : ∃ r : Step (d*m), (tail π r).1 ≠ (head π r).1 ∧
        T.val (tail π r).1 (head π r).1 ≠ true := by
      by_contra h
      apply hc
      intro r hr
      by_contra ha
      exact h ⟨r, hr, ha⟩
    apply Finset.prod_eq_zero (Finset.mem_univ r)
    simp [weight, tail_ne_head π r, hr, ha]

theorem pow_sub_div (E b : ℕ) (h : b ≤ E) :
    (2 : ℝ) ^ (E-b) / (2 : ℝ)^E = (1/2 : ℝ)^b := by
  rw [one_div_pow]
  apply (div_eq_div_iff (pow_ne_zero _ (by norm_num))
    (pow_ne_zero _ (by norm_num))).mpr
  rw [one_mul, ← pow_add, Nat.sub_add_cancel h]

/-- The probability of any genuine Hamilton path equals its weight-matrix monomial. -/
theorem path_probability_eq_weight {d m : ℕ} (T : Tournament d) (π : Arrangement d m) :
    ((Finset.univ.filter (fun ω : Sample d m => IsPath T ω π)).card : ℝ) /
        Fintype.card (Sample d m) = pathWeight T π := by
  classical
  rw [path_completion_count, card_sample, pathWeight_eq]
  split_ifs with hc
  · simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_sub_div _ _ (b_le π)
  · simp

/-- Swapping two finite sums proves the finite uniform-block expectation identity.
This theorem is not an asymptotic estimate. -/
theorem avgPath_eq_weightedPathSum {d m : ℕ} (T : Tournament d) :
    avgPath (m := m) T = weightedPathSum (m := m) T := by
  classical
  unfold avgPath weightedPathSum
  have hp : ∀ ω : Sample d m, (pathCount T ω : ℝ) =
      ∑ π : Arrangement d m, if IsPath T ω π then (1 : ℝ) else 0 := by
    intro ω
    symm
    exact Finset.sum_boole _ _
  simp_rw [hp]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro π _
  rw [Finset.sum_boole]
  exact path_probability_eq_weight T π

end
end UniformBlowup
