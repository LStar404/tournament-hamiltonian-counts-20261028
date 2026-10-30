module

public import TournamentHamiltonian.DenseMinorQuantitative
public import TournamentHamiltonian.PermanentEntryFrobenius
public import TournamentHamiltonian.GramLipschitz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
open scoped Matrix Matrix.Norms.L2Operator

namespace TournamentHamiltonian

noncomputable def denseBaseKernel {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := D - averagingMatrix (Fin n)

noncomputable def denseDeletedKernel {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (U : Finset (Fin n)) : Matrix (Uᶜ : Finset (Fin n)) (Uᶜ : Finset (Fin n)) ℝ :=
  densePrincipalMinor (denseBaseKernel D) U

noncomputable def denseProjectedKernel {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ)
    (U : Finset (Fin n)) : Matrix (Uᶜ : Finset (Fin n)) (Uᶜ : Finset (Fin n)) ℝ :=
  centeringProjection (Uᶜ : Finset (Fin n)) * denseDeletedKernel D U *
    centeringProjection (Uᶜ : Finset (Fin n))

theorem DenseStochastic.kernel_entry {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) (i j : Fin n) :
    |denseBaseKernel D i j| ≤ 4 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [denseBaseKernel, averagingMatrix, Matrix.sub_apply, Matrix.smul_apply,
    Fintype.card_fin, smul_eq_mul, Matrix.of_apply, mul_one]
  have h := abs_sub (D i j) ((n : ℝ)⁻¹)
  rw [abs_of_nonneg (hD.nonnegative i j), abs_of_pos (inv_pos.mpr hnR)] at h
  have hd := hD.density i j
  rw [div_eq_mul_inv] at hd ⊢
  linarith

theorem DenseStochastic.kernel_frobenius {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) : realFrobeniusNorm (denseBaseKernel D) ≤ 4 := by
  exact realFrobeniusNorm_le_entry_budget _ (by simpa using hn) 4 (by norm_num)
    (by simpa only [Fintype.card_fin] using hD.kernel_entry hn)

theorem DenseStochastic.kernel_centered {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) : DoublyCentered (denseBaseKernel D) := by
  have hp : 0 < Fintype.card (Fin n) := by simpa using hn
  constructor
  · intro i
    simp only [denseBaseKernel, Matrix.sub_apply, Finset.sum_sub_distrib,
      hD.row_sum, averagingMatrix_row_sum hp, sub_self]
  · intro j
    simp only [denseBaseKernel, Matrix.sub_apply, Finset.sum_sub_distrib,
      hD.column_sum, averagingMatrix_column_sum hp, sub_self]

theorem DenseStochastic.deleted_kernel_gap {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (U : Finset (Fin n)) : ‖denseDeletedKernel D U‖ ≤ 4 / 5 :=
  (submatrix_opNorm_le (denseBaseKernel D) Uᶜ Uᶜ).trans hD.gap

theorem DenseStochastic.deleted_kernel_marginals {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) :
    (∀ i, |∑ j, denseDeletedKernel D U i j| ≤ 4 * (U.card : ℝ) / n) ∧
    (∀ j, |∑ i, denseDeletedKernel D U i j| ≤ 4 * (U.card : ℝ) / n) := by
  have hr (i : Fin n) : |∑ j ∈ U, denseBaseKernel D i j| ≤ 4 * (U.card : ℝ) / n := by
    calc
      _ ≤ ∑ j ∈ U, |denseBaseKernel D i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ U, (4 : ℝ) / n := Finset.sum_le_sum (fun j _ => hD.kernel_entry hn i j)
      _ = _ := by simp; ring
  have hc (j : Fin n) : |∑ i ∈ U, denseBaseKernel D i j| ≤ 4 * (U.card : ℝ) / n := by
    calc
      _ ≤ ∑ i ∈ U, |denseBaseKernel D i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ U, (4 : ℝ) / n := Finset.sum_le_sum (fun i _ => hD.kernel_entry hn i j)
      _ = _ := by simp; ring
  constructor
  · intro i
    change |∑ j : (Uᶜ : Finset (Fin n)), denseBaseKernel D i j| ≤ _
    rw [Finset.sum_coe_sort Uᶜ (fun j => denseBaseKernel D i j),
      portedDeletionMass_sum_compl_eq_sub, (hD.kernel_centered hn).1, zero_sub, abs_neg]
    exact hr i
  · intro j
    change |∑ i : (Uᶜ : Finset (Fin n)), denseBaseKernel D i j| ≤ _
    rw [Finset.sum_coe_sort Uᶜ (fun i => denseBaseKernel D i j),
      portedDeletionMass_sum_compl_eq_sub, (hD.kernel_centered hn).2, zero_sub, abs_neg]
    exact hc j

/-- Actual deleted squared mass, counting the two coordinate directions separately. -/
theorem DenseStochastic.kernel_deleted_sq_mass {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) :
    (∑ i : U, ∑ j, denseBaseKernel D i j ^ 2) +
      (∑ j : U, ∑ i, denseBaseKernel D i j ^ 2) ≤ 32 * (U.card : ℝ) / n := by
  have hb (i j : Fin n) : denseBaseKernel D i j ^ 2 ≤ (4 / (n : ℝ)) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hD.kernel_entry hn i j) 2
  calc
    _ ≤ (∑ _i : U, ∑ _j : Fin n, (4 / (n : ℝ)) ^ 2) +
        (∑ _j : U, ∑ _i : Fin n, (4 / (n : ℝ)) ^ 2) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
      · exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hb i j))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe, nsmul_eq_mul]
      field_simp
      ring

/-- First Gram arrow: genuine row/column deletion, with changing dimensions. -/
theorem DenseStochastic.gram_deletion_log {n : ℕ}
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : DenseStochastic D) (hn : 0 < n)
    (U : Finset (Fin n)) :
    |Real.log (gramGaussian (denseDeletedKernel D U)) -
      Real.log (gramGaussian (denseBaseKernel D))| ≤ 50 * (U.card : ℝ) / n := by
  have h := gramGaussian_deletion_bound (denseBaseKernel D) Uᶜ Uᶜ
    (4 / 5) (by norm_num) (by norm_num) hD.gap
  change 0 ≤ Real.log (gramGaussian (denseBaseKernel D)) - Real.log (gramGaussian (denseDeletedKernel D U)) ∧
    Real.log (gramGaussian (denseBaseKernel D)) - Real.log (gramGaussian (denseDeletedKernel D U)) ≤
      ((∑ i : ((Uᶜ : Finset (Fin n))ᶜ : Finset (Fin n)), ∑ j, denseBaseKernel D i j ^ 2) +
        (∑ j : ((Uᶜ : Finset (Fin n))ᶜ : Finset (Fin n)), ∑ i, denseBaseKernel D i j ^ 2)) /
        (2 * (1 - (4 / 5 : ℝ) ^ 2)) at h
  rw [compl_compl U] at h
  rw [abs_sub_comm, abs_of_nonneg h.1]
  apply h.2.trans
  calc
    _ ≤ (32 * (U.card : ℝ) / n) / (2 * (1 - (4 / 5 : ℝ) ^ 2)) :=
      div_le_div_of_nonneg_right (hD.kernel_deleted_sq_mass hn U) (by norm_num)
    _ ≤ _ := by
      have ht : 0 ≤ (U.card : ℝ) / n := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      ring_nf at ht ⊢
      nlinarith

end TournamentHamiltonian
