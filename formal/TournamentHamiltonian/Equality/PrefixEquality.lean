module

public import TournamentHamiltonian.FiniteVectorOrder

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open scoped BigOperators

/-- Equality in the finite prefix-square comparison is rigid.
Only the lower vector needs to be decreasing and nonnegative; no assumption
on the upper vector beyond prefix domination and square-sum equality is used.
The statement also includes the empty vector. -/
theorem eq_of_finPrefix_le_of_sq_sum_eq {n : ℕ} (u v : Fin n → ℝ)
    (hu : DecreasingNonneg u)
    (hprefix : ∀ r ≤ n, finPrefixSum u r ≤ finPrefixSum v r)
    (hsq : (∑ i, u i ^ 2) = ∑ i, v i ^ 2) : u = v := by
  have hab := finite_dot_le_of_prefix_le u v u hu.1 hu.2 hprefix
  simp only [← pow_two] at hab
  have hnonneg : 0 ≤ ∑ i, (u i - v i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have heq : (∑ i, (u i - v i) ^ 2) =
      (∑ i, u i ^ 2) - 2 * (∑ i, v i * u i) + ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hzero : (∑ i, (u i - v i) ^ 2) = 0 := by linarith
  funext i
  have hi : (u i - v i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (u j - v j))).mp hzero i
      (Finset.mem_univ i)
  nlinarith [sq_nonneg (u i - v i)]

end TournamentHamiltonian
