module

public import TournamentHamiltonian.ForestQuartic.Concentration
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootObservable
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral ForestQuartic
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ}
def rootCoordinates (y : Fin (n+1) → ℝ) : Fin n → ℝ :=
  fun j => (y j.succ-y 0)/Real.sqrt (n+1 : ℝ)
def reconstruct (t : ℝ) (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  t • (1 : Fin (n+1) → ℝ) + Real.sqrt (n+1 : ℝ) • rootLift x

theorem sqrt_order_pos : 0 < Real.sqrt (n+1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
theorem sqrt_order_ne_zero : Real.sqrt (n+1 : ℝ) ≠ 0 := sqrt_order_pos.ne'

@[simp] theorem reconstruct_zero (t : ℝ) (x : Fin n → ℝ) : reconstruct t x 0 = t := by
  simp [reconstruct]
@[simp] theorem reconstruct_succ (t : ℝ) (x : Fin n → ℝ) (j : Fin n) :
    reconstruct t x j.succ = t+Real.sqrt (n+1 : ℝ)*x j := by simp [reconstruct]
@[simp] theorem rootCoordinates_reconstruct (t : ℝ) (x : Fin n → ℝ) :
    rootCoordinates (reconstruct t x) = x := by
  ext j
  simp [rootCoordinates, sqrt_order_ne_zero]
theorem reconstruct_rootCoordinates (y : Fin (n+1) → ℝ) :
    reconstruct (y 0) (rootCoordinates y) = y := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp [rootCoordinates, div_eq_mul_inv]
    field_simp [sqrt_order_ne_zero]
    ring

theorem K_one (F : EdgeSet (n+1)) : K F *ᵥ (1 : Fin (n+1) → ℝ) = 1 := by
  simp [K, complement, Matrix.sub_mulVec, Matrix.smul_mulVec, laplacian_mulVec_one]

theorem K_root_quadratic (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    (n+1 : ℝ) * (rootLift x ⬝ᵥ K F *ᵥ rootLift x) =
      x ⬝ᵥ rootMatrix F *ᵥ x + (∑ i, x i)^2 := by
  rw [root_quadratic_identity]
  have he : gaugeMatrix F = (n+1 : ℝ) • K F - ones := by
    unfold K
    push_cast
    rw [← fullMatrix_eq_scaled_complement]
    unfold gaugeMatrix fullMatrix
    ext i j
    simp
    ring
  rw [he, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    ones_mulVec, dotProduct_smul, dot_one]
  simp only [rootLift, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_add, smul_eq_mul]
  ring

/-- Genuine completed-square identity in anchor and grounded difference coordinates. -/
theorem quadratic_reconstruct (F : EdgeSet (n+1))
    (t : ℝ) (x : Fin n → ℝ) :
    reconstruct t x ⬝ᵥ K F *ᵥ reconstruct t x =
      (n+1 : ℝ)*(t+(∑ i, x i)/Real.sqrt (n+1 : ℝ))^2 + x ⬝ᵥ rootMatrix F *ᵥ x := by
  have hsym : (K F).IsSymm := by
    have hl := (laplacian_posSemidef F).isHermitian.isSymm
    ext i j
    simp only [K, complement, Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hl.apply]
    simp [Matrix.one_apply, eq_comm]
  have hcol : (1 : Fin (n+1) → ℝ) ᵥ* K F = 1 := by
    rw [← hsym, Matrix.vecMul_transpose, K_one]
  have hs : Real.sqrt (n+1 : ℝ)^2 = (n+1 : ℝ) := Real.sq_sqrt (by positivity)
  have hq := K_root_quadratic F x
  have hsx : ∑ i, rootLift x i = ∑ i, x i := by simp [rootLift, Fin.sum_univ_succ]
  have ho : (1 : Fin (n+1) → ℝ) ⬝ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) := by
    simp [dotProduct]
  simp only [reconstruct, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    add_dotProduct, smul_dotProduct, dotProduct_smul, K_one, smul_eq_mul]
  rw [Matrix.dotProduct_mulVec, hcol, ho]
  simp only [one_dot, dot_one, hsx]
  calc
    _ = (n+1 : ℝ)*t^2 + 2*t*Real.sqrt (n+1 : ℝ)*(∑ i, x i) +
        Real.sqrt (n+1 : ℝ)^2*(rootLift x ⬝ᵥ K F *ᵥ rootLift x) := by ring
    _ = (n+1 : ℝ)*t^2 + 2*t*Real.sqrt (n+1 : ℝ)*(∑ i, x i) +
        (x ⬝ᵥ rootMatrix F *ᵥ x + (∑ i, x i)^2) := by rw [hs, hq]
    _ = _ := by
      field_simp [sqrt_order_ne_zero]
      rw [hs]
      linear_combination -(n+1 : ℝ)*t^2*hs

/-- Actual linear phase is invariant under the anchor mode and scales by sqrt(m). -/
theorem phase_reconstruct (F : EdgeSet (n+1)) (t : ℝ) (x : Fin n → ℝ) :
    imbalance F ⬝ᵥ reconstruct t x = Real.sqrt (n+1 : ℝ)*(rootImbalance F ⬝ᵥ x) := by
  rw [reconstruct, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dot_one, sum_imbalance, root_phase_identity]
  simp only [smul_eq_mul, mul_zero, zero_add]

theorem phase_rootCoordinates (F : EdgeSet (n+1)) (y : Fin (n+1) → ℝ) :
    rootImbalance F ⬝ᵥ rootCoordinates y = (imbalance F ⬝ᵥ y)/Real.sqrt (n+1 : ℝ) := by
  have h := phase_reconstruct F (y 0) (rootCoordinates y)
  rw [reconstruct_rootCoordinates] at h
  rw [h]
  field_simp [sqrt_order_ne_zero]

end RootObservable
