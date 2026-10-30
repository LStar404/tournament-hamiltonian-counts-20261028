module

public import TournamentHamiltonian.UniformDeletion.Ratios

@[expose] public section

set_option autoImplicit false
namespace UniformDeletion
open TournamentHamiltonian UniformDenseLimit FixedDeletion Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual frozen uniform expected adjacency, with the very same Fin
reindexing as density. This is not a newly postulated matrix family. -/
def weightFin {d m : ℕ} (T : Tournament d) : Matrix (Fin (d*m)) (Fin (d*m)) ℝ :=
  Matrix.submatrix (UniformBlowup.weight T) finProdFinEquiv.symm finProdFinEquiv.symm

def weightScale (n : ℕ) : ℝ := ((n : ℝ)-1)/2

theorem density_eq_smul_weight {d m : ℕ} (T : Tournament d) :
    density (m := m) T = (2/((d*m : ℕ)-1 : ℝ)) • weightFin (m := m) T := rfl

theorem principal_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (U : Finset (Fin n)) (c : ℝ) :
    densePrincipalMinor (c • A) U = c • densePrincipalMinor A U := rfl

/-- Cycle homogeneity restores exactly the number of deleted vertices. The
identity remains valid if the original cycle count is zero (totalized division). -/
theorem cycle_scaled_ratio {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Finset (Fin n)) (c : ℝ) (hc : c ≠ 0) :
    WeightedCycle.cyc (densePrincipalMinor (c • A) U)/WeightedCycle.cyc (c • A) =
      (c⁻¹)^U.card*(WeightedCycle.cyc (densePrincipalMinor A U)/WeightedCycle.cyc A) := by
  have hk : U.card ≤ n := by simpa using U.card_le_univ
  rw [principal_smul, WeightedCycle.cyc_smul, WeightedCycle.cyc_smul]
  simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have he : c^n = c^U.card*c^(n-U.card) := by rw [← pow_add, Nat.add_sub_of_le hk]
  rw [he]
  by_cases hA : WeightedCycle.cyc A = 0
  · simp [hA]
  · field_simp
    rw [one_div_pow]
    field_simp

theorem path_scaled_ratio {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Finset (Fin n)) (hk : U.card < n) (c : ℝ) (hc : c ≠ 0) :
    WeightedCycle.path (densePrincipalMinor (c • A) U)/WeightedCycle.path (c • A) =
      (c⁻¹)^U.card*(WeightedCycle.path (densePrincipalMinor A U)/WeightedCycle.path A) := by
  rw [principal_smul, WeightedCycle.path_smul, WeightedCycle.path_smul]
  simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have he : c^(n-1) = c^U.card*c^(n-U.card-1) := by rw [← pow_add]; congr 1; omega
  rw [he]
  by_cases hA : WeightedCycle.path A = 0
  · simp [hA]
  · field_simp
    rw [one_div_pow]
    field_simp

theorem density_cycle_ratio_eq_weight {d m : ℕ} (T : Tournament d) (hN : 2 ≤ d*m)
    (U : Finset (Fin (d*m))) :
    WeightedCycle.cyc (densePrincipalMinor (density (m := m) T) U)/WeightedCycle.cyc (density (m := m) T) =
      weightScale (d*m)^U.card*(WeightedCycle.cyc (densePrincipalMinor (weightFin (m := m) T) U)/
        WeightedCycle.cyc (weightFin (m := m) T)) := by
  have hnR : (2 : ℝ) ≤ (d*m : ℕ) := by exact_mod_cast hN
  rw [density_eq_smul_weight, cycle_scaled_ratio _ _ _ (div_ne_zero (by norm_num) (by linarith))]
  congr 2
  simp [weightScale, div_eq_mul_inv]

theorem density_path_ratio_eq_weight {d m : ℕ} (T : Tournament d) (hN : 2 ≤ d*m)
    (U : Finset (Fin (d*m))) (hk : U.card < d*m) :
    WeightedCycle.path (densePrincipalMinor (density (m := m) T) U)/WeightedCycle.path (density (m := m) T) =
      weightScale (d*m)^U.card*(WeightedCycle.path (densePrincipalMinor (weightFin (m := m) T) U)/
        WeightedCycle.path (weightFin (m := m) T)) := by
  have hnR : (2 : ℝ) ≤ (d*m : ℕ) := by exact_mod_cast hN
  rw [density_eq_smul_weight, path_scaled_ratio _ _ hk _ (div_ne_zero (by norm_num) (by linarith))]
  congr 2
  simp [weightScale, div_eq_mul_inv]

/-- Restored unnormalized W ratios have the factor ((N-1)/2)^k, not factor one. -/
theorem actual_weight_deletion_ratios {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      0 < WeightedCycle.cyc (weightFin (m := m) T) ∧
      0 < WeightedCycle.path (weightFin (m := m) T) ∧
      ∀ U : Finset (Fin (d*m)), U.card = k →
        |weightScale (d*m)^k*(WeightedCycle.cyc (densePrincipalMinor (weightFin (m := m) T) U)/
            WeightedCycle.cyc (weightFin (m := m) T))-1| < ε ∧
        |weightScale (d*m)^k*(WeightedCycle.path (densePrincipalMinor (weightFin (m := m) T) U)/
            WeightedCycle.path (weightFin (m := m) T))-1| < ε := by
  intro ε hε
  filter_upwards [actual_density_deletion_ratios T hT hd k ε hε,
    UniformBlockMatrix.eventually_order_ge d (max 2 (k+1)) hd] with m h hm
  obtain ⟨hC,hH,hU⟩ := h
  have hN : 2 ≤ d*m := (le_max_left _ _).trans hm
  have hnR : (2 : ℝ) ≤ (d*m : ℕ) := by exact_mod_cast hN
  have hs : 0 < (2/((d*m : ℕ)-1 : ℝ)) := div_pos (by norm_num) (by linarith)
  rw [density_eq_smul_weight, WeightedCycle.cyc_smul] at hC
  rw [density_eq_smul_weight, WeightedCycle.path_smul] at hH
  refine ⟨(mul_pos_iff_of_pos_left (pow_pos hs _)).mp hC,
    (mul_pos_iff_of_pos_left (pow_pos hs _)).mp hH,?_⟩
  intro U hc
  have hk : U.card < d*m := by have := (le_max_right _ _).trans hm; omega
  have hu := hU U hc
  rw [density_cycle_ratio_eq_weight T hN U, hc] at hu
  rw [density_path_ratio_eq_weight T hN U hk, hc] at hu
  exact hu

/-- These are scalar normalization identities, not assumed triple-contraction
probabilities. The genuine contraction bijections belong to a later package. -/
theorem single_factor_normalization (n : ℕ) (x : ℝ) :
    ((n : ℝ)-1)^2*(x/4) = weightScale n^2*x := by unfold weightScale; ring

theorem double_factor_normalization (n : ℕ) (x : ℝ) :
    ((n : ℝ)-1)^4*(x/16) = weightScale n^4*x := by unfold weightScale; ring

/-- Both correctly normalized completion expressions, uniformly over all actual
2- and 4-vertex deletions. This does not identify either expression with an event. -/
theorem actual_weight_two_four_factors {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0 < d) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      (∀ U : Finset (Fin (d*m)), U.card = 2 →
        |((d*m : ℕ)-1 : ℝ)^2*((WeightedCycle.cyc (densePrincipalMinor (weightFin (m := m) T) U)/
          WeightedCycle.cyc (weightFin (m := m) T))/4)-1| < ε ∧
        |((d*m : ℕ)-1 : ℝ)^2*((WeightedCycle.path (densePrincipalMinor (weightFin (m := m) T) U)/
          WeightedCycle.path (weightFin (m := m) T))/4)-1| < ε) ∧
      (∀ U : Finset (Fin (d*m)), U.card = 4 →
        |((d*m : ℕ)-1 : ℝ)^4*((WeightedCycle.cyc (densePrincipalMinor (weightFin (m := m) T) U)/
          WeightedCycle.cyc (weightFin (m := m) T))/16)-1| < ε ∧
        |((d*m : ℕ)-1 : ℝ)^4*((WeightedCycle.path (densePrincipalMinor (weightFin (m := m) T) U)/
          WeightedCycle.path (weightFin (m := m) T))/16)-1| < ε) := by
  intro ε hε
  filter_upwards [actual_weight_deletion_ratios T hT hd 2 ε hε,
    actual_weight_deletion_ratios T hT hd 4 ε hε] with m h2 h4
  constructor
  · intro U hU
    simpa only [single_factor_normalization] using h2.2.2 U hU
  · intro U hU
    simpa only [double_factor_normalization] using h4.2.2 U hU

end
end UniformDeletion
