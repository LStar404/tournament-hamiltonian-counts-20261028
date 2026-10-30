module

public import TournamentHamiltonian.SkewGeometry
public import TournamentHamiltonian.CenteredPreconditioning
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Actual deterministic matrices of the uniform block model. -/
@[expose] public section

namespace UniformBlockMatrix
open TournamentHamiltonian
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section

abbrev Vertex (d m : ℕ) := Fin d × Fin m

/-- Regularity is the actual zero-score condition on the base tournament. -/
def IsRegular {d : ℕ} (T : Tournament d) : Prop := ∀ i, score T i = 0

def ones (ι : Type*) : Matrix ι ι ℝ := fun _ _ => 1

def signLift {d m : ℕ} (T : Tournament d) : Matrix (Vertex d m) (Vertex d m) ℝ :=
  fun u v => signMatrix T u.1 v.1

/-- The deterministic uniform-block weight matrix in block-algebra form.
`UniformBridge` identifies it with the frozen model's actual expected adjacency. -/
def weightMatrix {d m : ℕ} (T : Tournament d) : Matrix (Vertex d m) (Vertex d m) ℝ :=
  (1 / 2 : ℝ) • (ones (Vertex d m) - 1 + signLift T)

def density {d m : ℕ} (T : Tournament d) : Matrix (Vertex d m) (Vertex d m) ℝ :=
  (2 / ((d * m : ℕ) - 1 : ℝ)) • weightMatrix T

def centered {d m : ℕ} (T : Tournament d) : Matrix (Vertex d m) (Vertex d m) ℝ :=
  density T - (1 / (d * m : ℕ) : ℝ) • ones (Vertex d m)

@[simp] theorem card_vertex (d m : ℕ) : Fintype.card (Vertex d m) = d * m := by
  simp [Vertex]

theorem weightMatrix_eq_block {d m : ℕ} (T : Tournament d) :
    weightMatrix (m := m) T = (1 / 2 : ℝ) • (ones (Vertex d m) - 1 + signLift T) := rfl

/-- The three actual types of edges in the uniform model. -/
theorem weightMatrix_apply {d m : ℕ} (T : Tournament d) (u v : Vertex d m) :
    weightMatrix T u v =
      if u = v then 0 else if u.1 = v.1 then 1/2 else if T.val u.1 v.1 then 1 else 0 := by
  classical
  by_cases huv : u = v
  · subst v
    simp [weightMatrix, ones, signLift, signMatrix]
  by_cases hb : u.1 = v.1
  · simp [weightMatrix, ones, signLift, signMatrix, huv, hb]
  · cases ha : T.val u.1 v.1 <;>
      norm_num [weightMatrix, ones, signLift, signMatrix, huv, hb, ha, Matrix.one_apply]

theorem signLift_eq_kronecker {d m : ℕ} (T : Tournament d) :
    signLift (m := m) T = Matrix.kronecker (signMatrix T) (ones (Fin m)) := by
  ext u v
  simp [signLift, ones, Matrix.kronecker, Matrix.kroneckerMap]

theorem weightMatrix_nonneg {d m : ℕ} (T : Tournament d) (u v : Vertex d m) :
    0 ≤ weightMatrix T u v := by
  rw [weightMatrix_apply]
  split_ifs <;> norm_num

theorem weightMatrix_le_one {d m : ℕ} (T : Tournament d) (u v : Vertex d m) :
    weightMatrix T u v ≤ 1 := by
  rw [weightMatrix_apply]
  split_ifs <;> norm_num

@[simp] theorem weightMatrix_diag {d m : ℕ} (T : Tournament d) (u : Vertex d m) :
    weightMatrix T u u = 0 := by simp [weightMatrix_apply]

theorem signLift_row_sum {d m : ℕ} (T : Tournament d) (u : Vertex d m) :
    (∑ v, signLift T u v) = (m : ℝ) * score T u.1 := by
  simp [signLift, Fintype.sum_prod_type, score, ← Finset.mul_sum]

theorem signLift_col_sum {d m : ℕ} (T : Tournament d) (v : Vertex d m) :
    (∑ u, signLift T u v) = -(m : ℝ) * score T v.1 := by
  simp only [signLift, signMatrix_skew T _ v.1]
  rw [Finset.sum_neg_distrib]
  change -(∑ u, signLift T v u) = _
  rw [signLift_row_sum]
  ring

theorem weightMatrix_row_sum {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (u : Vertex d m) :
    (∑ v, weightMatrix T u v) = ((d * m : ℕ) - 1 : ℝ) / 2 := by
  classical
  rw [weightMatrix_eq_block]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    signLift_row_sum, hT u.1]
  simp [ones, Matrix.one_apply, div_eq_mul_inv, mul_comm]

theorem weightMatrix_col_sum {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (v : Vertex d m) :
    (∑ u, weightMatrix T u v) = ((d * m : ℕ) - 1 : ℝ) / 2 := by
  classical
  rw [weightMatrix_eq_block]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    signLift_col_sum, hT v.1]
  simp [ones, Matrix.one_apply, div_eq_mul_inv, mul_comm]

theorem density_nonneg {d m : ℕ} (T : Tournament d) (hN : 1 ≤ d * m)
    (u v : Vertex d m) : 0 ≤ density T u v := by
  have hNR : (1 : ℝ) ≤ (d * m : ℕ) := by exact_mod_cast hN
  exact mul_nonneg (div_nonneg (by norm_num) (sub_nonneg.mpr hNR))
    (weightMatrix_nonneg T u v)

theorem density_row_sum {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 1 < d * m) (u : Vertex d m) : (∑ v, density T u v) = 1 := by
  have hNR : (1 : ℝ) < (d * m : ℕ) := by exact_mod_cast hN
  simp only [density, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [weightMatrix_row_sum T hT]
  field_simp

theorem density_col_sum {d m : ℕ} (T : Tournament d) (hT : IsRegular T)
    (hN : 1 < d * m) (v : Vertex d m) : (∑ u, density T u v) = 1 := by
  have hNR : (1 : ℝ) < (d * m : ℕ) := by exact_mod_cast hN
  simp only [density, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [weightMatrix_col_sum T hT]
  field_simp

/-- The fixed density constant is valid already at total order three. -/
theorem density_entry_le {d m : ℕ} (T : Tournament d) (hN : 3 ≤ d * m)
    (u v : Vertex d m) : density T u v ≤ 3 / (d * m : ℕ) := by
  have hNR : (3 : ℝ) ≤ (d * m : ℕ) := by exact_mod_cast hN
  have hp : 0 < ((d * m : ℕ) : ℝ) - 1 := by linarith
  calc
    density T u v ≤ 2 / ((d * m : ℕ) - 1 : ℝ) := by
      exact mul_le_of_le_one_right (div_nonneg (by norm_num) hp.le)
        (weightMatrix_le_one T u v)
    _ ≤ _ := by
      apply (div_le_div_iff₀ hp (by linarith)).mpr
      nlinarith

/-- Centering exposes the contraction projection without any spectral hypothesis. -/
theorem centered_eq_projection {d m : ℕ} (T : Tournament d) (hN : 1 < d * m) :
    centered (m := m) T = (1 / ((d * m : ℕ) - 1 : ℝ)) •
      (signLift T - centeringProjection (Vertex d m)) := by
  have hNR : (1 : ℝ) < (d * m : ℕ) := by exact_mod_cast hN
  have h0 : ((d * m : ℕ) : ℝ) ≠ 0 := by linarith
  have h1 : ((d * m : ℕ) : ℝ) - 1 ≠ 0 := by linarith
  rw [centered, density, weightMatrix_eq_block, centeringProjection_eq]
  ext u v
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.add_apply,
    ones, Matrix.of_apply, card_vertex]
  field_simp
  ring

end
end UniformBlockMatrix
