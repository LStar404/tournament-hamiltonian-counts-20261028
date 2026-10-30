module

public import TournamentHamiltonian.DenseMinorKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

noncomputable def denseMinorInverseBudget : ℝ := localScalingInverseBudget 9 (9 / 10)

/-- One fixed positive deletion proportion, independent of the matrix and its size. -/
noncomputable def denseMinorDeletionThreshold : ℝ :=
  min (1 / 16) (min (1 / (2048 * denseMinorInverseBudget ^ 2))
    ((1 / 10) / (16 * (32 * denseMinorInverseBudget + 2))))

theorem denseMinorInverseBudget_pos : 0 < denseMinorInverseBudget := by
  norm_num [denseMinorInverseBudget, localScalingInverseBudget]

theorem denseMinorDeletionThreshold_pos : 0 < denseMinorDeletionThreshold := by
  norm_num [denseMinorDeletionThreshold, denseMinorInverseBudget, localScalingInverseBudget]

theorem denseMinorDeletionThreshold_bounds :
    denseMinorDeletionThreshold ≤ 1 / 16 ∧
      8 * denseMinorDeletionThreshold ≤ 1 / (256 * denseMinorInverseBudget ^ 2) ∧
      8 * denseMinorDeletionThreshold ≤
        (1 - 9 / 10) / (2 * (32 * denseMinorInverseBudget + 2)) := by
  norm_num [denseMinorDeletionThreshold, denseMinorInverseBudget, localScalingInverseBudget]

theorem dense_minor_small_proportion {n : ℕ} (hn : 0 < n) (U : Finset (Fin n))
    (hk : (U.card : ℝ) ≤ denseMinorDeletionThreshold * n) :
    (U.card : ℝ) ≤ (n : ℝ) / 16 ∧
      8 * (U.card : ℝ) / n ≤ 1 / (256 * denseMinorInverseBudget ^ 2) ∧
      8 * (U.card : ℝ) / n ≤
        (1 - 9 / 10) / (2 * (32 * denseMinorInverseBudget + 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (U.card : ℝ) / n ≤ denseMinorDeletionThreshold := (div_le_iff₀ hnR).mpr hk
  have he : 8 * (U.card : ℝ) / n ≤ 8 * denseMinorDeletionThreshold := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ht (by norm_num)
  refine ⟨?_, he.trans denseMinorDeletionThreshold_bounds.2.1,
    he.trans denseMinorDeletionThreshold_bounds.2.2⟩
  calc
    _ ≤ denseMinorDeletionThreshold * n := hk
    _ ≤ (1 / 16 : ℝ) * n := mul_le_mul_of_nonneg_right denseMinorDeletionThreshold_bounds.1 hnR.le
    _ = _ := by ring

/-- Actual principal-deletion balancing from only the fixed dense stochastic class.
All mass, density, centered gap, and marginal obligations are discharged here. -/
theorem exists_dense_minor_scaling_witness {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : DenseStochastic D) (hn : 0 < n) (U : Finset (Fin n))
    (hk : (U.card : ℝ) ≤ denseMinorDeletionThreshold * n) :
    ∃ z : ((Uᶜ : Finset (Fin n)) ⊕ (Uᶜ : Finset (Fin n))) → ℝ,
      LocalScalingWitness (massNormalizedMatrix (densePrincipalMinor D U))
        6 9 (9 / 10) (8 * (U.card : ℝ) / n) z := by
  have hs := dense_minor_small_proportion hn U hk
  have hb := hD.minor_basic hn U hs.1
  have hd := hD.normalized_minor_density hn U hs.1
  have hm := hD.normalized_minor_marginals hn U hs.1
  have ha := hD.normalized_minor_absolute_sums hn U hs.1
  exact exists_local_scaling_witness _ hb.1 (fun i j => (hd i j).1)
    (massNormalizedMatrix_mass _ hb.2.1.ne')
    6 9 (9 / 10) (8 * (U.card : ℝ) / n)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity)
    (fun i j => (hd i j).2) (hD.normalized_minor_kernel_density hn U hs.1)
    (hD.normalized_minor_gap hn U hs.1) hm.1 hm.2 ha.1 ha.2 hs.2.1 hs.2.2

/-- The same actual balancing potentials have the explicit quadratic capacity budget. -/
theorem exists_dense_minor_scaling_capacity {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : DenseStochastic D) (hn : 0 < n) (U : Finset (Fin n))
    (hk : (U.card : ℝ) ≤ denseMinorDeletionThreshold * n) :
    ∃ z : ((Uᶜ : Finset (Fin n)) ⊕ (Uᶜ : Finset (Fin n))) → ℝ,
      LocalScalingWitness (massNormalizedMatrix (densePrincipalMinor D U))
        6 9 (9 / 10) (8 * (U.card : ℝ) / n) z ∧
      localScalingCapacity z ≤ 4096 * denseMinorInverseBudget ^ 2 * (U.card : ℝ) ^ 2 / n := by
  obtain ⟨z,hz⟩ := exists_dense_minor_scaling_witness D hD hn U hk
  refine ⟨z,hz,?_⟩
  calc
    _ ≤ 32 * denseMinorInverseBudget ^ 2 *
        localEuclideanNorm (localMarginalVector (massNormalizedMatrix (densePrincipalMinor D U))) ^ 2 :=
      hz.capacity_upper
    _ ≤ 32 * denseMinorInverseBudget ^ 2 * (128 * (U.card : ℝ) ^ 2 / n) :=
      mul_le_mul_of_nonneg_left
        (hD.normalized_minor_marginal_sq hn U (dense_minor_small_proportion hn U hk).1) (by positivity)
    _ = _ := by ring

end TournamentHamiltonian
