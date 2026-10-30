module

public import TournamentHamiltonian.DenseMinorBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

theorem DenseStochastic.normalized_minor_density {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    ∀ i j, 0 ≤ massNormalizedMatrix (densePrincipalMinor D U) i j ∧
      |massNormalizedMatrix (densePrincipalMinor D U) i j| ≤
        6 / Fintype.card (Uᶜ : Finset (Fin n)) := by
  have hb := hD.minor_basic hn U hk
  have hM : (0 : ℝ) < Fintype.card (Uᶜ : Finset (Fin n)) := by exact_mod_cast hb.1
  have hMN : (Fintype.card (Uᶜ : Finset (Fin n)) : ℝ) ≤ n := by
    exact_mod_cast (show Fintype.card (Uᶜ : Finset (Fin n)) ≤ n by simp)
  intro i j
  have h0 := massNormalizedMatrix_nonnegative (densePrincipalMinor D U)
    (fun a b => hD.nonnegative a b) hb.2.1 i j
  refine ⟨h0, ?_⟩
  rw [abs_of_nonneg h0]
  change denseMinorAlpha D U * D i j ≤ _
  calc
    _ ≤ 2 * D i j := mul_le_mul_of_nonneg_right hb.2.2.2.2 (hD.nonnegative i j)
    _ ≤ 2 * (3 / n) := mul_le_mul_of_nonneg_left (hD.density i j) (by norm_num)
    _ = 6 / n := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hM hMN

/-- The normalized kernel is precisely a scaled centered compression of D-J/n. -/
theorem normalized_minor_centered_eq {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (U : Finset (Fin n)) (hp : 0 < Fintype.card (Uᶜ : Finset (Fin n)))
    (hM : matrixEntryMass (densePrincipalMinor D U) ≠ 0) :
    localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)) =
      denseMinorAlpha D U •
        (centeringProjection (Uᶜ : Finset (Fin n)) *
          densePrincipalMinor (D - averagingMatrix (Fin n)) U *
            centeringProjection (Uᶜ : Finset (Fin n))) := by
  rw [localCenteredKernel_eq_centering _ hp (massNormalizedMatrix_mass _ hM)]
  change centeringProjection (Uᶜ : Finset (Fin n)) *
    (denseMinorAlpha D U • densePrincipalMinor D U) * centeringProjection (Uᶜ : Finset (Fin n)) = _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  have hQ : densePrincipalMinor D U = densePrincipalMinor (D - averagingMatrix (Fin n)) U +
      ((n : ℝ)⁻¹) • Matrix.of (fun (_ : (Uᶜ : Finset (Fin n))) (_ : (Uᶜ : Finset (Fin n))) => (1 : ℝ)) := by
    ext i j
    simp only [densePrincipalMinor, Matrix.submatrix_apply, Matrix.sub_apply, averagingMatrix,
      Matrix.smul_apply, Matrix.of_apply, Matrix.add_apply, Fintype.card_fin, smul_eq_mul, mul_one]
    ring
  rw [hQ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    centeringProjection_mul_ones hp, smul_zero, Matrix.zero_mul, add_zero]

theorem DenseStochastic.normalized_minor_gap {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    ‖localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U))‖ ≤ 9 / 10 := by
  have hb := hD.minor_basic hn U hk
  have ha : 0 ≤ denseMinorAlpha D U := by linarith [hb.2.2.1]
  have hcomp : ‖densePrincipalMinor (D - averagingMatrix (Fin n)) U‖ ≤ 4 / 5 :=
    (submatrix_opNorm_le (D - averagingMatrix (Fin n)) Uᶜ Uᶜ).trans hD.gap
  have hcenter := centeredMatrix_opNorm_le
    (densePrincipalMinor (D - averagingMatrix (Fin n)) U) hb.1 hb.1
  have hscale := mul_le_mul_of_nonneg_left (hcenter.trans hcomp) ha
  rw [normalized_minor_centered_eq D U hb.1 hb.2.1.ne', norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ha]
  apply hscale.trans
  have ht : (U.card : ℝ) / n ≤ 1 / 16 :=
    (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr (by linarith)
  have he := hb.2.2.2.1
  rw [mul_div_assoc] at he
  nlinarith

theorem DenseStochastic.normalized_minor_kernel_density {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    ∀ i j, |localCenteredKernel (massNormalizedMatrix (densePrincipalMinor D U)) i j| ≤
      9 / Fintype.card (Uᶜ : Finset (Fin n)) := by
  have hb := hD.minor_basic hn U hk
  have hm := hD.normalized_minor_marginals hn U hk
  have hd := hD.normalized_minor_density hn U hk
  have heps : 8 * (U.card : ℝ) / n ≤ 1 / 2 :=
    (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr (by linarith)
  intro i j
  exact (localCenteredKernel_density_bound _ hb.1 6 (8*U.card/n)
    (fun a b => (hd a b).2) hm.1 hm.2 i j).trans
      (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

theorem DenseStochastic.normalized_minor_absolute_sums {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    (∀ i, ∑ j, |massNormalizedMatrix (densePrincipalMinor D U) i j| ≤ 2) ∧
    (∀ j, ∑ i, |massNormalizedMatrix (densePrincipalMinor D U) i j| ≤ 2) := by
  have hm := hD.normalized_minor_marginals hn U hk
  have hd := hD.normalized_minor_density hn U hk
  have heps : 8 * (U.card : ℝ) / n ≤ 1 / 2 :=
    (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr (by linarith)
  constructor
  · intro i
    simp_rw [abs_of_nonneg (hd i _).1]
    have h := (abs_le.mp (hm.1 i)).2
    unfold matrixRowError at h
    linarith
  · intro j
    simp_rw [abs_of_nonneg (hd _ j).1]
    have h := (abs_le.mp (hm.2 j)).2
    unfold matrixColumnError at h
    linarith

theorem DenseStochastic.normalized_minor_marginal_sq {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    localEuclideanNorm (localMarginalVector (massNormalizedMatrix (densePrincipalMinor D U))) ^ 2 ≤
      128 * (U.card : ℝ) ^ 2 / n := by
  have hm := hD.normalized_minor_marginals hn U hk
  have hMN : (Fintype.card (Uᶜ : Finset (Fin n)) : ℝ) ≤ n := by
    exact_mod_cast (show Fintype.card (Uᶜ : Finset (Fin n)) ≤ n by simp)
  rw [localMarginalVector_euclidean_sq]
  calc
    _ ≤ (∑ _i : (Uᶜ : Finset (Fin n)), (8 * (U.card : ℝ) / n) ^ 2) +
        ∑ _j : (Uᶜ : Finset (Fin n)), (8 * (U.card : ℝ) / n) ^ 2 := by
      apply add_le_add
      · apply Finset.sum_le_sum; intro i _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hm.1 i) 2
      · apply Finset.sum_le_sum; intro j _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hm.2 j) 2
    _ = 2 * (Fintype.card (Uᶜ : Finset (Fin n)) : ℝ) * (8 * (U.card : ℝ) / n) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ 2 * (n : ℝ) * (8 * (U.card : ℝ) / n) ^ 2 := by gcongr
    _ = _ := by field_simp; ring

end TournamentHamiltonian
