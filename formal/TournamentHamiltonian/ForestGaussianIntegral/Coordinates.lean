module

public import TournamentHamiltonian.ForestGaussian.Factor
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace ForestGaussianIntegral
open Matrix
open scoped BigOperators
noncomputable section

variable {n : ℕ}
def ones : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := fun _ _ => 1
def rootLift (x : Fin n → ℝ) : Fin (n+1) → ℝ := Fin.cons 0 x
def rootTail (x : Fin (n+1) → ℝ) : Fin n → ℝ := fun i => x i.succ

def centered (x : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  x - ((∑ i, x i) / (n+1 : ℝ)) • (1 : Fin (n+1) → ℝ)

def gauge (x : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  x - x 0 • (1 : Fin (n+1) → ℝ)

def reduced (H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (H - ones).submatrix Fin.succ Fin.succ

@[simp] theorem rootLift_zero (x : Fin n → ℝ) : rootLift x 0 = 0 := rfl
@[simp] theorem rootLift_succ (x : Fin n → ℝ) (i : Fin n) : rootLift x i.succ = x i := rfl
@[simp] theorem rootTail_lift (x : Fin n → ℝ) : rootTail (rootLift x) = x := rfl
@[simp] theorem gauge_zero (x : Fin (n+1) → ℝ) : gauge x 0 = 0 := by simp [gauge]

theorem ones_mulVec (x : Fin (n+1) → ℝ) :
    ones *ᵥ x = (∑ i, x i) • (1 : Fin (n+1) → ℝ) := by
  ext i
  simp [ones, Matrix.mulVec, dotProduct]

theorem ones_isHermitian : (ones (n := n)).IsHermitian := by
  ext i j
  simp [ones, Matrix.conjTranspose_apply]

theorem one_dot (x : Fin (n+1) → ℝ) : (1 : Fin (n+1) → ℝ) ⬝ᵥ x = ∑ i, x i := by
  simp [dotProduct]

theorem dot_one (x : Fin (n+1) → ℝ) : x ⬝ᵥ (1 : Fin (n+1) → ℝ) = ∑ i, x i := by
  simp [dotProduct]

theorem col_sum {H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hH : H.IsHermitian)
    (hrow : H *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ)) :
    (1 : Fin (n+1) → ℝ) ᵥ* H = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ) := by
  rw [← hH.isSymm, Matrix.vecMul_transpose]
  exact hrow

theorem sum_mulVec {H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ} (hH : H.IsHermitian)
    (hrow : H *ᵥ (1 : Fin (n+1) → ℝ) = (n+1 : ℝ) • (1 : Fin (n+1) → ℝ))
    (x : Fin (n+1) → ℝ) :
    (∑ i, (H *ᵥ x) i) = (n+1 : ℝ) * (∑ i, x i) := by
  rw [← one_dot, Matrix.dotProduct_mulVec, col_sum hH hrow, smul_dotProduct, one_dot]
  simp

theorem rootLift_dot (x : Fin n → ℝ) (y : Fin (n+1) → ℝ) :
    rootLift x ⬝ᵥ y = x ⬝ᵥ rootTail y := by
  simp [dotProduct, Fin.sum_univ_succ, rootLift, rootTail]

theorem reduced_mulVec (H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (x : Fin n → ℝ) :
    reduced H *ᵥ x = rootTail ((H - ones) *ᵥ rootLift x) := by
  ext i
  simp [reduced, rootTail, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, rootLift]

theorem reduced_quadratic (H : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (reduced H *ᵥ x) = rootLift x ⬝ᵥ ((H - ones) *ᵥ rootLift x) := by
  rw [reduced_mulVec, rootLift_dot]

theorem gauge_eq_lift_tail (x : Fin (n+1) → ℝ) : gauge x = rootLift (rootTail (gauge x)) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · rfl

theorem centered_lift_ne_zero (x : Fin n → ℝ) (hx : x ≠ 0) : centered (rootLift x) ≠ 0 := by
  intro hz
  have h0 := congrFun hz 0
  have hmean : (∑ i, rootLift x i) / (n+1 : ℝ) = 0 := by
    change 0 - ((∑ i, rootLift x i) / (n+1 : ℝ)) * 1 = 0 at h0
    linarith
  apply hx
  ext i
  have h := congrFun hz i.succ
  change x i - ((∑ i, rootLift x i) / (n+1 : ℝ)) * 1 = 0 at h
  change x i = 0
  simpa only [hmean, zero_mul, sub_zero] using h

end
end ForestGaussianIntegral
