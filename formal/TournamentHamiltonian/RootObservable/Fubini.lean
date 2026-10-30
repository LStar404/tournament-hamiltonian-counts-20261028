module

public import TournamentHamiltonian.RootObservable.Coordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootObservable
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral ForestQuartic PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

def gaussianMode (n : ℕ) (t : ℝ) : ℝ := Real.exp (-((n+1 : ℝ)/2)*t^2)
def modeMass (n : ℕ) : ℝ := Real.sqrt (2*Real.pi/(n+1 : ℝ))
def jacobianFactor (n : ℕ) : ℝ := Real.sqrt (n+1 : ℝ)^n * modeMass n

theorem gaussianMode_integrable (n : ℕ) : Integrable (gaussianMode n) :=
  integrable_exp_neg_mul_sq (by positivity)
theorem gaussianMode_integral (n : ℕ) : (∫ t, gaussianMode n t) = modeMass n := by
  change (∫ t : ℝ, Real.exp (-((n+1 : ℝ)/2)*t^2)) = _
  rw [integral_gaussian, modeMass]
  congr 1
  field_simp

theorem gaussianMode_shift_integrable (n : ℕ) (c : ℝ) :
    Integrable (fun t => gaussianMode n (t+c)) :=
  (gaussianMode_integrable n).comp_add_right c

theorem gaussianMode_shift_integral (n : ℕ) (c : ℝ) :
    (∫ t, gaussianMode n (t+c)) = modeMass n := by
  rw [integral_add_right_eq_self, gaussianMode_integral]

theorem shifted_product_integrable (g : (Fin n → ℝ) → ℝ) (hg : Integrable g)
    (hgm : Measurable g) (c : (Fin n → ℝ) → ℝ) (hc : Measurable c) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => gaussianMode n (p.1+c p.2)*g p.2) := by
  have hm : Measurable (fun p : (Fin n → ℝ) × ℝ => gaussianMode n (p.2+c p.1)*g p.1) := by
    unfold gaussianMode
    fun_prop
  have hs : Integrable (fun p : (Fin n → ℝ) × ℝ => gaussianMode n (p.2+c p.1)*g p.1) := by
    change Integrable _ ((volume : Measure (Fin n → ℝ)).prod (volume : Measure ℝ))
    rw [integrable_prod_iff hm.aestronglyMeasurable]
    constructor
    · exact ae_of_all _ (fun x => (gaussianMode_shift_integrable n (c x)).mul_const (g x))
    · have he (x : Fin n → ℝ) : (∫ t, ‖gaussianMode n (t+c x)*g x‖) = modeMass n*‖g x‖ := by
        simp only [norm_mul, Real.norm_eq_abs, gaussianMode, abs_of_pos (Real.exp_pos _)]
        rw [integral_mul_const]
        exact congrArg (fun v => v*|g x|) (gaussianMode_shift_integral n (c x))
      simp_rw [he]
      exact hg.norm.const_mul _
  exact hs.swap

theorem shifted_product_integral (g : (Fin n → ℝ) → ℝ) (hg : Integrable g)
    (hgm : Measurable g) (c : (Fin n → ℝ) → ℝ) (hc : Measurable c) :
    (∫ t, ∫ x, gaussianMode n (t+c x)*g x) = modeMass n*(∫ x, g x) := by
  rw [integral_integral_swap (shifted_product_integrable g hg hgm c hc)]
  simp_rw [integral_mul_const, gaussianMode_shift_integral]
  rw [integral_const_mul]

theorem kernel_reconstruct (F : EdgeSet (n+1)) (t : ℝ) (x : Fin n → ℝ) :
    kernelDensity F (reconstruct t x) =
      gaussianMode n (t+(∑ i, x i)/Real.sqrt (n+1 : ℝ)) * realKernel (rootMatrix F) 0 x := by
  unfold kernelDensity realKernel gaussianMode
  simp only [zero_dotProduct, add_zero]
  rw [quadratic_reconstruct, ← Real.exp_add]
  congr 1
  ring

/-- The actual tail-coordinate Lebesgue Jacobian, independent of Gaussian formulas. -/
theorem tail_substitution (H : (Fin (n+1) → ℝ) → ℝ) (t : ℝ) :
    (∫ u : Fin n → ℝ, H (Fin.cons t u)) =
      Real.sqrt (n+1 : ℝ)^n * ∫ x, H (reconstruct t x) := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (Fin n → ℝ))
    (fun u => H (Fin.cons t (u+(fun _ => t)))) (Real.sqrt (n+1 : ℝ))
    (hR := sqrt_order_pos.le)
  have he (x : Fin n → ℝ) : Fin.cons t (Real.sqrt (n+1 : ℝ) • x + (fun _ => t)) = reconstruct t x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [add_comm]
  simp only [he, Module.finrank_pi, Fintype.card_fin, smul_eq_mul] at h
  rw [integral_add_right_eq_self (fun u : Fin n → ℝ => H (Fin.cons t u)) (fun _ => t)] at h
  have hn : Real.sqrt (n+1 : ℝ)^n ≠ 0 := pow_ne_zero _ sqrt_order_ne_zero
  rw [h]
  field_simp

/-- Split the genuine Pi-Lebesgue volume into root value and remaining coordinates. -/
theorem integral_split_root (H : (Fin (n+1) → ℝ) → ℝ) (hH : Integrable H) :
    (∫ y, H y) = ∫ t, ∫ u, H (Fin.cons t u) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have hp : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ _
  have hpi := hp.symm.integrable_comp_of_integrable hH
  have he (p : ℝ × (Fin n → ℝ)) : e.symm p = Fin.cons p.1 p.2 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [e]
  rw [← hp.symm.integral_comp' H]
  change (∫ p, H (e.symm p) ∂(volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) = _
  calc
    _ = ∫ t, ∫ u, H (e.symm (t,u)) := integral_prod (fun p => H (e.symm p)) hpi
    _ = _ := by simp only [he]

end RootObservable
