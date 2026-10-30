module

public import TournamentHamiltonian.LocalScalingComplete
public import TournamentHamiltonian.ScalingKernelBridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

/-- Fixed actual dense doubly stochastic class; the gap uses the real L2 operator norm. -/
structure DenseStochastic {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) : Prop where
  nonnegative : ∀ i j, 0 ≤ D i j
  row_sum : ∀ i, ∑ j, D i j = 1
  column_sum : ∀ j, ∑ i, D i j = 1
  density : ∀ i j, D i j ≤ 3 / n
  gap : ‖D - averagingMatrix (Fin n)‖ ≤ 4 / 5

noncomputable def densePrincipalMinor {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (U : Finset (Fin n)) : Matrix (Uᶜ : Finset (Fin n)) (Uᶜ : Finset (Fin n)) ℝ :=
  D.submatrix Subtype.val Subtype.val

noncomputable def denseRemovedMass {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (U : Finset (Fin n)) : ℝ := ∑ i ∈ U, ∑ j ∈ U, D i j

noncomputable def denseMinorAlpha {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (U : Finset (Fin n)) : ℝ :=
  (Fintype.card (Uᶜ : Finset (Fin n)) : ℝ) / matrixEntryMass (densePrincipalMinor D U)

theorem DenseStochastic.mass {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) : matrixEntryMass D = n := by
  simp [matrixEntryMass, hD.row_sum]

theorem DenseStochastic.deleted_mass {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (U : Finset (Fin n)) :
    matrixEntryMass (densePrincipalMinor D U) = (n : ℝ) - 2 * U.card + denseRemovedMass D U := by
  rw [densePrincipalMinor, matrixEntryMass_deleted, hD.mass]
  simp only [hD.row_sum, hD.column_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  unfold denseRemovedMass
  ring

theorem DenseStochastic.removed_row_bounds {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (U : Finset (Fin n)) (i : Fin n) :
    0 ≤ ∑ j ∈ U, D i j ∧ (∑ j ∈ U, D i j) ≤ 3 * U.card / n ∧
      (∑ j ∈ U, D i j) ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun j _ => hD.nonnegative i j), ?_, ?_⟩
  · calc
      _ ≤ ∑ _j ∈ U, (3 : ℝ) / n := Finset.sum_le_sum (fun j _ => hD.density i j)
      _ = _ := by simp; ring
  · rw [← hD.row_sum i]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hD.nonnegative i j)

theorem DenseStochastic.removed_column_bounds {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (U : Finset (Fin n)) (j : Fin n) :
    0 ≤ ∑ i ∈ U, D i j ∧ (∑ i ∈ U, D i j) ≤ 3 * U.card / n ∧
      (∑ i ∈ U, D i j) ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => hD.nonnegative i j), ?_, ?_⟩
  · calc
      _ ≤ ∑ _i ∈ U, (3 : ℝ) / n := Finset.sum_le_sum (fun i _ => hD.density i j)
      _ = _ := by simp; ring
  · rw [← hD.column_sum j]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hD.nonnegative i j)

theorem DenseStochastic.removed_mass_bounds {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (U : Finset (Fin n)) :
    0 ≤ denseRemovedMass D U ∧ denseRemovedMass D U ≤ U.card ∧
      denseRemovedMass D U ≤ 3 * (U.card : ℝ) ^ 2 / n := by
  refine ⟨Finset.sum_nonneg (fun i _ => (hD.removed_row_bounds U i).1), ?_, ?_⟩
  · calc
      _ ≤ ∑ _i ∈ U, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hD.removed_row_bounds U i).2.2)
      _ = _ := by simp
  · calc
      _ ≤ ∑ _i ∈ U, 3 * (U.card : ℝ) / n :=
        Finset.sum_le_sum (fun i _ => (hD.removed_row_bounds U i).2.1)
      _ = _ := by simp; ring

/-- Scalar normalization bounds, with every denominator proved positive. -/
theorem dense_minor_scalar_bounds (N k s : ℝ) (hN : 0 < N) (hk : 0 ≤ k)
    (hsmall : k ≤ N / 16) (hs0 : 0 ≤ s) (hsk : s ≤ k) :
    0 < N - k ∧ 0 < N - 2 * k + s ∧
      1 ≤ (N - k) / (N - 2 * k + s) ∧
      (N - k) / (N - 2 * k + s) ≤ 1 + 2 * k / N ∧
      (N - k) / (N - 2 * k + s) ≤ 2 := by
  have hM : 0 < N - k := by linarith
  have hH : 0 < N - 2 * k + s := by linarith
  have hlo : 1 ≤ (N - k) / (N - 2 * k + s) := by
    apply (le_div_iff₀ hH).mpr
    linarith
  have hhi : (N - k) / (N - 2 * k + s) ≤ 1 + 2 * k / N := by
    apply (div_le_iff₀ hH).mpr
    apply (mul_le_mul_iff_left₀ hN).mp
    have hprod : N * (N - k) ≤ (N + 2 * k) * (N - 2 * k + s) := by
      nlinarith [mul_nonneg hk (show 0 ≤ N - 4*k by linarith),
        mul_nonneg hs0 (show 0 ≤ N + 2*k by linarith)]
    convert hprod using 1 <;> field_simp <;> ring
  have ht : k / N ≤ 1 / 16 := (div_le_iff₀ hN).mpr (by linarith)
  exact ⟨hM,hH,hlo,hhi,hhi.trans (by rw [mul_div_assoc]; linarith)⟩

theorem DenseStochastic.minor_basic {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) (U : Finset (Fin n))
    (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    0 < Fintype.card (Uᶜ : Finset (Fin n)) ∧
      0 < matrixEntryMass (densePrincipalMinor D U) ∧
      1 ≤ denseMinorAlpha D U ∧ denseMinorAlpha D U ≤ 1 + 2 * U.card / n ∧
      denseMinorAlpha D U ≤ 2 := by
  have hcard : (Fintype.card (Uᶜ : Finset (Fin n)) : ℝ) = (n : ℝ) - U.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, Nat.cast_sub (show U.card ≤ n by simpa using U.card_le_univ)]
  have h := dense_minor_scalar_bounds (n : ℝ) U.card (denseRemovedMass D U)
    (by exact_mod_cast hn) (Nat.cast_nonneg _) hk (hD.removed_mass_bounds U).1
      (hD.removed_mass_bounds U).2.1
  have hp : 0 < Fintype.card (Uᶜ : Finset (Fin n)) := by exact_mod_cast (hcard ▸ h.1)
  simpa only [denseMinorAlpha, hcard, hD.deleted_mass U] using
    (show 0 < Fintype.card (Uᶜ : Finset (Fin n)) ∧ _ from ⟨hp,h.2⟩)

theorem DenseStochastic.minor_row_error {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (U : Finset (Fin n)) (i : (Uᶜ : Finset (Fin n))) :
    matrixRowError (densePrincipalMinor D U) i = -(∑ j ∈ U, D i j) := by
  simp only [matrixRowError, densePrincipalMinor, Matrix.submatrix_apply, Finset.sum_coe_sort]
  rw [portedDeletionMass_sum_compl_eq_sub, hD.row_sum]
  ring

theorem DenseStochastic.minor_column_error {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (U : Finset (Fin n)) (j : (Uᶜ : Finset (Fin n))) :
    matrixColumnError (densePrincipalMinor D U) j = -(∑ i ∈ U, D i j) := by
  change (∑ i : (Uᶜ : Finset (Fin n)), D i j) - 1 = _
  rw [Finset.sum_coe_sort (Uᶜ) (fun i : Fin n => D i j),
    portedDeletionMass_sum_compl_eq_sub, hD.column_sum]
  ring

theorem dense_normalized_defect_le (a r t : ℝ) (ha : 1 ≤ a) (ha2 : a ≤ 2)
    (hat : a ≤ 1 + 2*t) (hr : 0 ≤ r) (hrt : r ≤ 3*t) (ht : 0 ≤ t) :
    |a * (-r) + (a - 1)| ≤ 8*t := by
  have har : 0 ≤ a*r := mul_nonneg (by linarith) hr
  have har' : a*r ≤ 6*t := by nlinarith [mul_le_mul_of_nonneg_right ha2 hr]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem DenseStochastic.normalized_minor_marginals {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) (hk : (U.card : ℝ) ≤ (n : ℝ) / 16) :
    (∀ i, |matrixRowError (massNormalizedMatrix (densePrincipalMinor D U)) i| ≤ 8 * U.card / n) ∧
    (∀ j, |matrixColumnError (massNormalizedMatrix (densePrincipalMinor D U)) j| ≤ 8 * U.card / n) := by
  have hb := hD.minor_basic hn U hk
  have ht : 0 ≤ (U.card : ℝ) / n := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  constructor
  · intro i
    rw [massNormalizedMatrix, matrixRowError_smul, hD.minor_row_error]
    change |denseMinorAlpha D U * (-(∑ j ∈ U, D i j)) + (denseMinorAlpha D U - 1)| ≤ _
    convert dense_normalized_defect_le (denseMinorAlpha D U) _ ((U.card : ℝ) / n)
      hb.2.2.1 hb.2.2.2.2 (by convert hb.2.2.2.1 using 1 <;> ring)
      (hD.removed_row_bounds U i).1 (by convert (hD.removed_row_bounds U i).2.1 using 1 <;> ring) ht using 1 <;> ring
  · intro j
    rw [massNormalizedMatrix, matrixColumnError_smul, hD.minor_column_error]
    change |denseMinorAlpha D U * (-(∑ i ∈ U, D i j)) + (denseMinorAlpha D U - 1)| ≤ _
    convert dense_normalized_defect_le (denseMinorAlpha D U) _ ((U.card : ℝ) / n)
      hb.2.2.1 hb.2.2.2.2 (by convert hb.2.2.2.1 using 1 <;> ring)
      (hD.removed_column_bounds U j).1 (by convert (hD.removed_column_bounds U j).2.1 using 1 <;> ring) ht using 1 <;> ring

end TournamentHamiltonian
