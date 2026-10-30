module

public import TournamentHamiltonian.PDGaussian.Boundary

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootGaussianTail
open Matrix MeasureTheory ForestGaussianIntegral PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Unnormalized, genuine complete-root Gaussian density on n real coordinates. -/
def density (n : ℕ) (a : ℝ) (x : Fin n → ℝ) : ℝ :=
  realKernel (a • completeRoot n) 0 x

/-- Actual Lebesgue integral, not a proxy chosen to fit a formula. -/
def partition (n : ℕ) (a : ℝ) : ℝ := ∫ x : Fin n → ℝ, density n a x

/-- Vertex-count notation: p vertices, p−1 root-fixed coordinates. -/
def Z (p : ℕ) (a : ℝ) : ℝ := partition (p-1) a

def tilted (n : ℕ) (a : ℝ) (i : Fin n) (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(x ⬝ᵥ (a • completeRoot n) *ᵥ x)/2 + s*x i)

theorem density_exp (n : ℕ) (a : ℝ) (x : Fin n → ℝ) :
    density n a x = Real.exp (-(x ⬝ᵥ (a • completeRoot n) *ᵥ x)/2) := by
  simp [density, realKernel]

theorem density_nonneg (n : ℕ) (a : ℝ) (x : Fin n → ℝ) : 0 ≤ density n a x := by
  rw [density_exp]
  positivity

theorem density_integrable (n : ℕ) (a : ℝ) (ha : 0 < a) : Integrable (density n a) :=
  realKernel_integrable (scaled_completeRoot_posDef n a ha) 0

theorem partition_eq (n : ℕ) (a : ℝ) (ha : 0 < a) :
    partition n a = normalization (a • completeRoot n) :=
  zero_integral (scaled_completeRoot_posDef n a ha)

theorem partition_pos (n : ℕ) (a : ℝ) (ha : 0 < a) : 0 < partition n a := by
  rw [partition_eq n a ha]
  exact normalization_pos (scaled_completeRoot_posDef n a ha)

theorem tilted_integrable (n : ℕ) (a : ℝ) (ha : 0 < a) (i : Fin n) (s : ℝ) :
    Integrable (tilted n a i s) := complete_coordinate_integrable n a ha i s

theorem tilted_integral (n : ℕ) (a : ℝ) (ha : 0 < a) (i : Fin n) (s : ℝ) :
    (∫ x : Fin n → ℝ, tilted n a i s x) =
      partition n a * Real.exp (s^2/(a*(n+1 : ℝ))) := by
  have h := complete_coordinate_MGF n a ha i s
  change (∫ x : Fin n → ℝ, tilted n a i s x) / partition n a = _ at h
  rw [div_eq_iff (ne_of_gt (partition_pos n a ha))] at h
  exact h.trans (mul_comm _ _)
end RootGaussianTail
