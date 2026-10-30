module

public import TournamentHamiltonian.DenseMinorWitness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

/-- A finite scalar conversion of the existing displacement estimate. -/
theorem dense_minor_frobenius_scalar (N M k L u : ℝ)
    (hN : 0 < N) (hM : N / 4 ≤ M) (hk : 0 ≤ k) (hL : 0 ≤ L)
    (hu : 0 ≤ u) (hu2 : u ^ 2 ≤ 128 * k ^ 2 / N) :
    (8 * 6 * L / Real.sqrt M) * u ≤ 1536 * L * k / N := by
  have hM0 : 0 < M := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
  have huB : u ≤ 16 * k / Real.sqrt N := by
    apply (sq_le_sq₀ hu (div_nonneg (by positivity) hsN.le)).mp
    calc
      u ^ 2 ≤ 128 * k ^ 2 / N := hu2
      _ ≤ 256 * k ^ 2 / N := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg k]) hN.le
      _ = _ := by rw [div_pow, Real.sq_sqrt hN.le]; ring
  have hroot : Real.sqrt N ≤ 2 * Real.sqrt M := by
    apply (sq_le_sq₀ hsN.le (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hN.le, Real.sq_sqrt hM0.le]
    nlinarith
  have hcoef : 8 * 6 * L / Real.sqrt M ≤ 96 * L / Real.sqrt N := by
    apply (div_le_div_iff₀ hsM hsN).mpr
    nlinarith [mul_le_mul_of_nonneg_left hroot (show 0 ≤ 48*L by positivity)]
  calc
    _ ≤ (96 * L / Real.sqrt N) * (16 * k / Real.sqrt N) :=
      mul_le_mul hcoef huB hu (by positivity)
    _ = 1536 * L * k / (Real.sqrt N) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt hN.le]

/-- One and the same true balancing witness, with explicit capacity and
Frobenius budgets uniform in D, U and n. -/
theorem exists_dense_minor_scaling_quantitative {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ denseMinorDeletionThreshold * n) :
    ∃ z : ((Uᶜ : Finset (Fin n)) ⊕ (Uᶜ : Finset (Fin n))) → ℝ,
      LocalScalingWitness (massNormalizedMatrix (densePrincipalMinor D U))
        6 9 (9 / 10) (8 * (U.card : ℝ) / n) z ∧
      localScalingCapacity z ≤ 4096 * denseMinorInverseBudget ^ 2 * (U.card : ℝ) ^ 2 / n ∧
      realFrobeniusNorm (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z -
        massNormalizedMatrix (densePrincipalMinor D U)) ≤
          1536 * denseMinorInverseBudget * U.card / n := by
  obtain ⟨z,hz,hcap⟩ := exists_dense_minor_scaling_capacity D hD hn U hk
  have hk16 := (dense_minor_small_proportion hn U hk).1
  have hcard : (Fintype.card (Uᶜ : Finset (Fin n)) : ℝ) = (n : ℝ) - U.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
      Nat.cast_sub (show U.card ≤ n by simpa using U.card_le_univ)]
  have hM : (n : ℝ) / 4 ≤ Fintype.card (Uᶜ : Finset (Fin n)) := by
    rw [hcard]
    linarith
  refine ⟨z,hz,hcap,hz.frobenius.trans ?_⟩
  exact dense_minor_frobenius_scalar n (Fintype.card (Uᶜ : Finset (Fin n)))
    U.card denseMinorInverseBudget
    (localEuclideanNorm (localMarginalVector (massNormalizedMatrix (densePrincipalMinor D U))))
    (by exact_mod_cast hn) hM (Nat.cast_nonneg _) denseMinorInverseBudget_pos.le
    (localEuclideanNorm_nonneg _) (hD.normalized_minor_marginal_sq hn U hk16)

end TournamentHamiltonian
