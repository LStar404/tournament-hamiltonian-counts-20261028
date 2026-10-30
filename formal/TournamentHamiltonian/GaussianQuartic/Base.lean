module

public import TournamentHamiltonian.GaussianMoments
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace GaussianQuartic
open MeasureTheory ProbabilityTheory TournamentHamiltonian
open scoped BigOperators
noncomputable section

abbrev gaussian (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem coordinates_independent :
    iIndepFun (fun i (z : ι → ℝ) => z i) (gaussian ι) :=
  iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)

theorem restrict_preserving (f : κ → ι) (hf : Function.Injective f) :
    MeasurePreserving (fun z : ι → ℝ => fun i => z (f i)) (gaussian ι) (gaussian κ) := by
  refine ⟨by fun_prop, ?_⟩
  have h := (coordinates_independent (ι := ι)).precomp hf
  rw [h.map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) (f i)).map_eq

theorem integral_restrict (f : κ → ι) (hf : Function.Injective f)
    (g : (κ → ℝ) → ℝ) (hg : Measurable g) :
    (∫ z, g (fun i => z (f i)) ∂gaussian ι) = ∫ z, g z ∂gaussian κ := by
  rw [← (restrict_preserving f hf).map_eq]
  exact (integral_map (restrict_preserving f hf).measurable.aemeasurable hg.aestronglyMeasurable).symm

def polynomial {d n : ℕ} (c : Fin n → ℝ) (e : Fin n → Fin d → ℕ)
    (z : Fin d → ℝ) : ℝ := ∑ t, c t * ∏ i, z i ^ e t i

theorem polynomial_integrable {d n : ℕ} (c : Fin n → ℝ) (e : Fin n → Fin d → ℕ) :
    Integrable (polynomial c e) (gaussian (Fin d)) := by
  exact integrable_finsetSum _ (fun t _ => (standardGaussian_product_integrable (e t)).const_mul _)

theorem polynomial_integral {d n : ℕ} (c : Fin n → ℝ) (e : Fin n → Fin d → ℕ) :
    (∫ z, polynomial c e z ∂gaussian (Fin d)) =
      ∑ t, c t * ∏ i, standardGaussianMoment (e t i) := by
  simp only [polynomial]
  rw [integral_finsetSum _ (fun t _ =>
    (standardGaussian_product_integrable (e t)).const_mul _)]
  simp only [integral_const_mul, standardGaussian_product_moment]

@[simp] theorem moment_0 : standardGaussianMoment 0 = 1 := standardGaussianMoment_zero
@[simp] theorem moment_1 : standardGaussianMoment 1 = 0 := standardGaussianMoment_one
@[simp] theorem moment_2 : standardGaussianMoment 2 = 1 := by
  simpa using standardGaussianMoment_add_two 0
@[simp] theorem moment_3 : standardGaussianMoment 3 = 0 := by
  simpa using standardGaussianMoment_add_two 1
@[simp] theorem moment_4 : standardGaussianMoment 4 = 3 := by
  have h := standardGaussianMoment_add_two 2
  norm_num at h ⊢
  exact h
@[simp] theorem moment_5 : standardGaussianMoment 5 = 0 := by
  simpa using standardGaussianMoment_add_two 3
@[simp] theorem moment_6 : standardGaussianMoment 6 = 15 := by
  have h := standardGaussianMoment_add_two 4
  norm_num at h ⊢
  exact h
@[simp] theorem moment_7 : standardGaussianMoment 7 = 0 := by
  simpa using standardGaussianMoment_add_two 5
@[simp] theorem moment_8 : standardGaussianMoment 8 = 105 := by
  have h := standardGaussianMoment_add_two 6
  norm_num at h ⊢
  exact h

end
end GaussianQuartic
