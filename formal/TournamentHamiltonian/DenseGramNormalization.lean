module

public import TournamentHamiltonian.DenseGramDeletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

/-- A row-sum bound controls the actual normalized constant-vector action. -/
theorem flat_action_sq_le_of_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : Matrix ι ι ℝ) (hp : 0 < Fintype.card ι) (r : ℝ)
    (hrow : ∀ i, |∑ j, Z i j| ≤ r) :
    (∑ i, (Z *ᵥ flatUnitVector ι) i ^ 2) ≤ r ^ 2 := by
  have hpR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hp
  have heq : (∑ i, (Z *ᵥ flatUnitVector ι) i ^ 2) =
      (∑ i, (∑ j, Z i j) ^ 2) / Fintype.card ι := by
    simp only [Matrix.mulVec, dotProduct, flatUnitVector, ← Finset.sum_mul, mul_pow,
      inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), div_eq_mul_inv]
  rw [heq]
  calc
    _ ≤ (∑ _i : ι, r ^ 2) / Fintype.card ι := by
      apply div_le_div_of_nonneg_right _ hpR.le
      apply Finset.sum_le_sum; intro i _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hrow i) 2
    _ = _ := by simp [mul_div_cancel_left₀ _ hpR.ne']

theorem DenseStochastic.projected_kernel_bounds {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    ‖denseProjectedKernel D U‖ ≤ 4 / 5 ∧ realFrobeniusNorm (denseProjectedKernel D U) ≤ 4 := by
  have hp := (hD.minor_basic hn U hk).1
  exact ⟨(centeredMatrix_opNorm_le _ hp hp).trans (hD.deleted_kernel_gap U),
    (centeredMatrix_frobenius_le _ hp hp).trans
      ((realFrobeniusNorm_submatrix_le (denseBaseKernel D) Uᶜ Uᶜ).trans (hD.kernel_frobenius hn))⟩

/-- Second Gram arrow: actual two-sided projection off the remaining flat direction. -/
theorem DenseStochastic.gram_centering_log {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    |Real.log (gramGaussian (denseProjectedKernel D U)) -
      Real.log (gramGaussian (denseDeletedKernel D U))| ≤ 50 * (U.card : ℝ) / n := by
  have hp := (hD.minor_basic hn U hk).1
  have hm := hD.deleted_kernel_marginals hn U
  have hr := flat_action_sq_le_of_rows (denseDeletedKernel D U) hp (4*U.card/n) hm.1
  have hc := flat_action_sq_le_of_rows (denseDeletedKernel D U).transpose hp (4*U.card/n) hm.2
  have h := gramGaussian_centering_bound (denseDeletedKernel D U) hp hp
    (4 / 5) (by norm_num) (by norm_num) (hD.deleted_kernel_gap U)
  change 0 ≤ Real.log (gramGaussian (denseDeletedKernel D U)) -
    Real.log (gramGaussian (denseProjectedKernel D U)) ∧ _ at h
  rw [abs_sub_comm, abs_of_nonneg h.1]
  apply h.2.trans
  have ht : (U.card : ℝ) / n ≤ 1 :=
    (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr (by linarith)
  have ht0 : 0 ≤ (U.card : ℝ) / n := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ (2 * (4 * (U.card : ℝ) / n) ^ 2) / (2 * (1 - (4 / 5 : ℝ) ^ 2)) :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    _ ≤ _ := by
      have ht2 : ((U.card : ℝ) / n)^2 ≤ (U.card : ℝ) / n := by nlinarith
      ring_nf at ht0 ht2 ⊢
      nlinarith

theorem DenseStochastic.normalized_kernel_frobenius {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    realFrobeniusNorm (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U))) ≤ 8 ∧
    realFrobeniusNorm (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)) -
      denseProjectedKernel D U) ≤ 8 * (U.card : ℝ) / n := by
  have hb := hD.minor_basic hn U hk
  have hv := (hD.projected_kernel_bounds hn U hk).2
  have ha0 : 0 ≤ denseMinorAlpha D U := by linarith [hb.2.2.1]
  have ha1 : 0 ≤ denseMinorAlpha D U - 1 := by linarith [hb.2.2.1]
  have heq : localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)) =
      denseMinorAlpha D U • denseProjectedKernel D U :=
    normalized_minor_centered_eq D U hb.1 hb.2.1.ne'
  constructor
  · rw [heq, realFrobeniusNorm_smul, abs_of_nonneg ha0]
    have h := mul_le_mul hb.2.2.2.2 hv (realFrobeniusNorm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
    norm_num at h
    exact h
  · have hdiff : localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)) -
        denseProjectedKernel D U = (denseMinorAlpha D U - 1) • denseProjectedKernel D U := by
      rw [heq, sub_smul, one_smul]
    rw [hdiff, realFrobeniusNorm_smul, abs_of_nonneg ha1]
    calc
      _ ≤ (2 * (U.card : ℝ) / n) * 4 :=
        mul_le_mul (by linarith [hb.2.2.2.1]) hv (realFrobeniusNorm_nonneg _) (by positivity)
      _ = _ := by ring

/-- Third Gram arrow: the actual mass normalization, with its fixed dimension. -/
theorem DenseStochastic.gram_normalization_log {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    |Real.log (gramGaussian (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)))) -
      Real.log (gramGaussian (denseProjectedKernel D U))| ≤ 300 * (U.card : ℝ) / n := by
  have hf := hD.normalized_kernel_frobenius hn U hk
  have hv := hD.projected_kernel_bounds hn U hk
  have h := gramGaussian_log_lipschitz
    (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U))) (denseProjectedKernel D U)
    (9/10) (by norm_num) (by norm_num) (hD.normalized_minor_gap hn U hk) (hv.1.trans (by norm_num))
  have hprod := mul_le_mul (show realFrobeniusNorm
      (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U))) +
      realFrobeniusNorm (denseProjectedKernel D U) ≤ 12 by linarith [hf.1,hv.2])
    hf.2 (realFrobeniusNorm_nonneg _) (by norm_num : (0:ℝ) ≤ 12)
  apply h.trans
  calc
    _ ≤ (12 * (8 * (U.card : ℝ) / n)) / (2 * (1 - (9/10:ℝ)^2)) :=
      div_le_div_of_nonneg_right hprod (by norm_num)
    _ ≤ _ := by
      have ht : 0 ≤ (U.card : ℝ) / n := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      ring_nf at ht ⊢
      nlinarith

theorem DenseStochastic.gram_normalized_minor_log {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    |Real.log (gramGaussian (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)))) -
      Real.log (gramGaussian (denseBaseKernel D))| ≤ 400 * (U.card : ℝ) / n := by
  have h1 := hD.gram_deletion_log hn U
  have h2 := hD.gram_centering_log hn U hk
  have h3 := hD.gram_normalization_log hn U hk
  have ha := abs_sub_le
    (Real.log (gramGaussian (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)))))
    (Real.log (gramGaussian (denseProjectedKernel D U)))
    (Real.log (gramGaussian (denseDeletedKernel D U)))
  have hb := abs_sub_le
    (Real.log (gramGaussian (localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)))))
    (Real.log (gramGaussian (denseDeletedKernel D U)))
    (Real.log (gramGaussian (denseBaseKernel D)))
  exact hb.trans ((add_le_add (ha.trans (add_le_add h3 h2)) h1).trans_eq (by ring))

end TournamentHamiltonian
