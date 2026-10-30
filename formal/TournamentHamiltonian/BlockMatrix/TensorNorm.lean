module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option autoImplicit false
@[expose] public section
open scoped BigOperators Matrix.Norms.L2Operator Kronecker

namespace UniformBlockMatrix
noncomputable section

/-- Lift a base matrix by replacing each entry by a constant `m × m` block. -/
def blockLift {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℝ :=
  fun u v => S u.1 v.1

@[simp] theorem blockLift_apply {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (u v : Fin d × Fin m) : blockLift S u v = S u.1 v.1 := rfl

/-- Exact Kronecker identity, with an all-ones matrix rather than an identity matrix. -/
theorem blockLift_eq_kronecker {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    blockLift (m := m) S = S ⊗ₖ (fun (_ _ : Fin m) => (1 : ℝ)) := by
  ext u v
  change S u.1 v.1 = S u.1 v.1 * 1
  exact (mul_one _).symm

/-- Sum coordinates inside each block. -/
def blockSum {d m : ℕ} (x : EuclideanSpace ℝ (Fin d × Fin m)) :
    EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun i => ∑ a : Fin m, x (i, a))

/-- Cauchy--Schwarz controls the block-summing map uniformly, including `m = 0`. -/
theorem blockSum_norm_sq_le {d m : ℕ} (x : EuclideanSpace ℝ (Fin d × Fin m)) :
    ‖blockSum x‖ ^ 2 ≤ (m : ℝ) * ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  change (∑ i : Fin d, (∑ a : Fin m, x (i, a)) ^ 2) ≤ _
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
    (fun _ => (1 : ℝ)) (fun a => x (i, a))

/-- The lifted action is constant on each block. -/
theorem blockLift_action {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d × Fin m)) (u : Fin d × Fin m) :
    Matrix.toEuclideanCLM (n := Fin d × Fin m) (𝕜 := ℝ) (blockLift S) x u =
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) S (blockSum x) u.1 := by
  change (∑ v : Fin d × Fin m, S u.1 v.1 * x v) =
    ∑ j : Fin d, S u.1 j * ∑ a : Fin m, x (j, a)
  simp only [Fintype.sum_prod_type, Finset.mul_sum]

/-- Repetition across each output block multiplies the squared norm by `m`. -/
theorem blockLift_action_norm_sq {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d × Fin m)) :
    ‖Matrix.toEuclideanCLM (n := Fin d × Fin m) (𝕜 := ℝ) (blockLift S) x‖ ^ 2 =
      (m : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) S (blockSum x)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, blockLift_action, Fintype.sum_prod_type]
  simp [← Finset.mul_sum]

/-- The operator norm of `S ⊗ J_m` is at most `m ‖S‖`. -/
theorem blockLift_opNorm_le {d m : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) :
    ‖blockLift (m := m) S‖ ≤ (m : ℝ) * ‖S‖ := by
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [blockLift_action_norm_sq]
  have hact : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) S (blockSum x)‖ ≤
      ‖S‖ * ‖blockSum x‖ := by
    simpa only [Matrix.l2_opNorm_toEuclideanCLM] using
      ContinuousLinearMap.le_opNorm (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) S) (blockSum x)
  calc
    _ ≤ (m : ℝ) * (‖S‖ * ‖blockSum x‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hact 2) (Nat.cast_nonneg _)
    _ = (m : ℝ) * ‖S‖ ^ 2 * ‖blockSum x‖ ^ 2 := by ring
    _ ≤ (m : ℝ) * ‖S‖ ^ 2 * ((m : ℝ) * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (blockSum_norm_sq_le x) (by positivity)
    _ = _ := by ring

end
end UniformBlockMatrix
