module

public import TournamentHamiltonian.LocalLogCos.Error
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LocalLogCos
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral RootObservable PDGaussian Filter
open scoped Topology BigOperators

def cutoff (m : ℕ) : ℝ := (m : ℝ)^(-(7/16 : ℝ))
def cutoffError (m : ℕ) : ℝ := 32*(m : ℝ)^(-(5/8 : ℝ))

theorem cutoff_nonneg (m : ℕ) : 0 ≤ cutoff m := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem cutoff_tendsto : Tendsto cutoff atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/16)).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem cutoff_eventually_quarter : ∀ᶠ m : ℕ in atTop, cutoff m ≤ Real.pi/8 :=
  cutoff_tendsto.eventually (eventually_le_nhds (by positivity : (0:ℝ)<Real.pi/8))

theorem errorBudget_cutoff (m : ℕ) (hm : 1 ≤ m) : errorBudget m (cutoff m) = cutoffError m := by
  have hm0 : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  unfold errorBudget cutoff cutoffError
  rw [← Real.rpow_mul_natCast hm0.le]
  have h2 : (m : ℝ)^2 = (m : ℝ)^(2:ℝ) := (Real.rpow_natCast _ 2).symm
  rw [h2, mul_assoc, ← Real.rpow_add hm0]
  congr 2
  norm_num

theorem cutoffError_tendsto : Tendsto cutoffError atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ => (32:ℝ)*(m:ℝ)^(-(5/8:ℝ))) atTop (𝓝 0)
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<5/8)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 32
  simpa only [Function.comp_def, mul_zero] using h

/-- At the fixed m^(-7/16) cutoff, the pointwise Gaussian-relative Taylor error is 32 m^(-5/8). -/
theorem cutoff_cosProduct_error {n : ℕ} (F : EdgeSet (n+1)) (hc : cutoff (n+1) ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox (cutoff (n+1)) x) :
    |cosProduct F x-realKernel (rootMatrix F) 0 x*Real.exp (-rootQuartic F x)| ≤
      cutoffError (n+1)*realKernel (rootMatrix F) 0 x := by
  have h := cosProduct_error F (cutoff_nonneg _) hc hx
  rwa [errorBudget_cutoff _ (by omega)] at h

end LocalLogCos
