module

public import TournamentHamiltonian.DenseGramNormalization
public import TournamentHamiltonian.ScaledGaussianComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

noncomputable def denseMinorGramConstant : ℝ := 400 + 200000 * denseMinorInverseBudget

theorem denseMinorGramConstant_pos : 0 < denseMinorGramConstant := by
  unfold denseMinorGramConstant
  linarith [denseMinorInverseBudget_pos]

/-- Every genuine witness has the same proved dense-minor displacement budget. -/
theorem DenseStochastic.witness_frobenius {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16)
    (z : ((Uᶜ : Finset (Fin n)) ⊕ (Uᶜ : Finset (Fin n))) → ℝ)
    (hz : LocalScalingWitness (massNormalizedMatrix (densePrincipalMinor D U))
      6 9 (9 / 10) (8 * (U.card : ℝ) / n) z) :
    realFrobeniusNorm (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z -
      massNormalizedMatrix (densePrincipalMinor D U)) ≤ 1536 * denseMinorInverseBudget * U.card / n := by
  have hcard : (Fintype.card (Uᶜ : Finset (Fin n)) : ℝ) = (n : ℝ) - U.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
      Nat.cast_sub (show U.card ≤ n by simpa using U.card_le_univ)]
  have hM : (n : ℝ) / 4 ≤ Fintype.card (Uᶜ : Finset (Fin n)) := by rw [hcard]; linarith
  exact hz.frobenius.trans (dense_minor_frobenius_scalar n (Fintype.card (Uᶜ : Finset (Fin n)))
    U.card denseMinorInverseBudget _ (by exact_mod_cast hn) hM (Nat.cast_nonneg _)
    denseMinorInverseBudget_pos.le (localEuclideanNorm_nonneg _) (hD.normalized_minor_marginal_sq hn U hk))

/-- Fourth Gram arrow, using the same potentials and actual centered scaled matrix. -/
theorem DenseStochastic.gram_scaling_log {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16)
    (z : ((Uᶜ : Finset (Fin n)) ⊕ (Uᶜ : Finset (Fin n))) → ℝ)
    (hz : LocalScalingWitness (massNormalizedMatrix (densePrincipalMinor D U))
      6 9 (9 / 10) (8 * (U.card : ℝ) / n) z) :
    |Real.log (gramGaussian (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z -
        averagingMatrix (Uᶜ : Finset (Fin n)))) -
      Real.log (gramGaussian (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U))))| ≤
        200000 * denseMinorInverseBudget * U.card / n := by
  let X := massNormalizedMatrix (densePrincipalMinor D U)
  let Y := localScaledMatrix X z
  let W := Y - averagingMatrix (Uᶜ : Finset (Fin n))
  let E := localCenteredKernel X
  have hb := hD.minor_basic hn U hk
  have hpR : (0 : ℝ) < Fintype.card (Uᶜ : Finset (Fin n)) := by exact_mod_cast hb.1
  have hYc : centeringProjection (Uᶜ : Finset (Fin n)) * Y * centeringProjection (Uᶜ : Finset (Fin n)) = W := by
    have ha : rectangularAverageMatrix (Uᶜ : Finset (Fin n)) (Uᶜ : Finset (Fin n)) =
        averagingMatrix (Uᶜ : Finset (Fin n)) := by
      ext i j
      simp [rectangularAverageMatrix, averagingMatrix]
    have h := rectangular_unit_marginals_centering Y (Equiv.refl _) hb.1 hz.row_sum hz.column_sum
    rw [ha] at h
    exact h
  have hEc : E = centeringProjection (Uᶜ : Finset (Fin n)) * X * centeringProjection (Uᶜ : Finset (Fin n)) :=
    localCenteredKernel_eq_centering X hb.1 (massNormalizedMatrix_mass _ hb.2.1.ne')
  have hdiff : W - E = centeringProjection (Uᶜ : Finset (Fin n)) * (Y-X) *
      centeringProjection (Uᶜ : Finset (Fin n)) := by
    rw [← hYc, hEc, Matrix.mul_sub, Matrix.sub_mul]
  have hdisp : realFrobeniusNorm (W-E) ≤ 1536 * denseMinorInverseBudget * U.card / n := by
    rw [hdiff]
    exact (centeredMatrix_frobenius_le _ hb.1 hb.1).trans (hD.witness_frobenius hn U hk z hz)
  have hWf : realFrobeniusNorm W ≤ 13 := by
    apply realFrobeniusNorm_le_entry_budget W hb.1 13 (by norm_num)
    intro i j
    change |Y i j - averagingMatrix (Uᶜ : Finset (Fin n)) i j| ≤ _
    have h := abs_sub (Y i j) (averagingMatrix (Uᶜ : Finset (Fin n)) i j)
    have havg : |averagingMatrix (Uᶜ : Finset (Fin n)) i j| = 1 / Fintype.card (Uᶜ : Finset (Fin n)) := by
      simp [averagingMatrix, abs_of_pos (inv_pos.mpr hpR), one_div]
    rw [havg] at h
    have hy := hz.density i j
    change |Y i j| ≤ 2*6/Fintype.card (Uᶜ : Finset (Fin n)) at hy
    calc
      _ ≤ |Y i j| + 1 / Fintype.card (Uᶜ : Finset (Fin n)) := h
      _ ≤ 2*6/Fintype.card (Uᶜ : Finset (Fin n)) + 1/Fintype.card (Uᶜ : Finset (Fin n)) :=
        add_le_add hy le_rfl
      _ = _ := by ring
  have hEf : realFrobeniusNorm E ≤ 8 := (hD.normalized_kernel_frobenius hn U hk).1
  have hWq : ‖W‖ ≤ (19/20 : ℝ) := hz.gap.trans (by norm_num)
  have hEq : ‖E‖ ≤ (19/20 : ℝ) := (hD.normalized_minor_gap hn U hk).trans (by norm_num)
  have h := gramGaussian_log_lipschitz W E (19/20) (by norm_num) (by norm_num) hWq hEq
  have hp := mul_le_mul (show realFrobeniusNorm W + realFrobeniusNorm E ≤ 22 by linarith)
    hdisp (realFrobeniusNorm_nonneg _) (by norm_num : (0:ℝ) ≤ 22)
  apply h.trans
  calc
    _ ≤ (22 * (1536 * denseMinorInverseBudget * U.card / n)) / (2 * (1 - (19/20:ℝ)^2)) :=
      div_le_div_of_nonneg_right hp (by norm_num)
    _ ≤ _ := by
      have ht : 0 ≤ denseMinorInverseBudget * ((U.card : ℝ) / n) :=
        mul_nonneg denseMinorInverseBudget_pos.le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      ring_nf at ht ⊢
      nlinarith

theorem DenseStochastic.gram_scaled_minor_log {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16)
    (z : ((Uᶜ : Finset (Fin n)) ⊕ (Uᶜ : Finset (Fin n))) → ℝ)
    (hz : LocalScalingWitness (massNormalizedMatrix (densePrincipalMinor D U))
      6 9 (9 / 10) (8 * (U.card : ℝ) / n) z) :
    |Real.log (gramGaussian (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z -
        averagingMatrix (Uᶜ : Finset (Fin n)))) - Real.log (gramGaussian (denseBaseKernel D))| ≤
      denseMinorGramConstant * U.card / n := by
  have h1 := hD.gram_scaling_log hn U hk z hz
  have h2 := hD.gram_normalized_minor_log hn U hk
  have h := abs_sub_le
    (Real.log (gramGaussian (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z -
      averagingMatrix (Uᶜ : Finset (Fin n)))))
    (Real.log (gramGaussian (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)))))
    (Real.log (gramGaussian (denseBaseKernel D)))
  apply h.trans
  calc
    _ ≤ 200000 * denseMinorInverseBudget * U.card / n + 400 * (U.card : ℝ) / n := add_le_add h1 h2
    _ = _ := by unfold denseMinorGramConstant; ring

/-- Exact mass and exponential restoration for the actual retained permanent. -/
theorem DenseStochastic.minor_permanent_restoration {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16)
    (z : ((Uᶜ : Finset (Fin n)) ⊕ (Uᶜ : Finset (Fin n))) → ℝ) :
    (densePrincipalMinor D U).permanent = Real.exp (-localScalingCapacity z) *
      (matrixEntryMass (densePrincipalMinor D U) / Fintype.card (Uᶜ : Finset (Fin n))) ^
        Fintype.card (Uᶜ : Finset (Fin n)) *
      (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z).permanent := by
  have hb := hD.minor_basic hn U hk
  have hpR : (0 : ℝ) < Fintype.card (Uᶜ : Finset (Fin n)) := by exact_mod_cast hb.1
  have hr : 0 < matrixEntryMass (densePrincipalMinor D U) / Fintype.card (Uᶜ : Finset (Fin n)) :=
    div_pos hb.2.1 hpR
  have hl : Real.log (Fintype.card (Uᶜ : Finset (Fin n)) / matrixEntryMass (densePrincipalMinor D U)) =
      -Real.log (matrixEntryMass (densePrincipalMinor D U) / Fintype.card (Uᶜ : Finset (Fin n))) := by
    rw [Real.log_div hpR.ne' hb.2.1.ne', Real.log_div hb.2.1.ne' hpR.ne']
    ring
  rw [normalized_local_scaling_permanent_restoration _ hb.1 hb.2.1 z, hl]
  rw [show -(localScalingCapacity z + Fintype.card (Uᶜ : Finset (Fin n)) *
      -Real.log (matrixEntryMass (densePrincipalMinor D U) / Fintype.card (Uᶜ : Finset (Fin n)))) =
      -localScalingCapacity z + Fintype.card (Uᶜ : Finset (Fin n)) *
      Real.log (matrixEntryMass (densePrincipalMinor D U) / Fintype.card (Uᶜ : Finset (Fin n))) by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log hr]

/-- The four actual Gram arrows and exact permanent identity, for the same z
constructed without any extra analytic hypotheses. -/
theorem exists_dense_minor_gram_restoration {n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ denseMinorDeletionThreshold * n) :
    ∃ z : ((Uᶜ : Finset (Fin n)) ⊕ (Uᶜ : Finset (Fin n))) → ℝ,
      LocalScalingWitness (massNormalizedMatrix (densePrincipalMinor D U))
        6 9 (9 / 10) (8 * (U.card : ℝ) / n) z ∧
      localScalingCapacity z ≤ 4096 * denseMinorInverseBudget ^ 2 * (U.card : ℝ) ^ 2 / n ∧
      |Real.log (gramGaussian (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z -
          averagingMatrix (Uᶜ : Finset (Fin n)))) - Real.log (gramGaussian (denseBaseKernel D))| ≤
        denseMinorGramConstant * U.card / n ∧
      (densePrincipalMinor D U).permanent = Real.exp (-localScalingCapacity z) *
        (matrixEntryMass (densePrincipalMinor D U) / Fintype.card (Uᶜ : Finset (Fin n))) ^
          Fintype.card (Uᶜ : Finset (Fin n)) *
        (localScaledMatrix (massNormalizedMatrix (densePrincipalMinor D U)) z).permanent := by
  obtain ⟨z,hz,hcap,_⟩ := exists_dense_minor_scaling_quantitative D hD hn U hk
  have hsmall := (dense_minor_small_proportion hn U hk).1
  exact ⟨z,hz,hcap,hD.gram_scaled_minor_log hn U hsmall z hz,
    hD.minor_permanent_restoration hn U hsmall z⟩

end TournamentHamiltonian
