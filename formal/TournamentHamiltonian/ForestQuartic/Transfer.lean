module

public import TournamentHamiltonian.ForestQuartic.TiltBridge

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ForestQuartic
open MeasureTheory ProbabilityTheory GaussianQuartic ForestGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem memLp_tilt_integrable {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m)
    {g : (Fin m → ℝ) → ℝ} (hg : MemLp g 2 (gaussian (Fin m))) :
    Integrable g (tiltedMeasure F) := by
  rw [tiltedMeasure, integrable_tilted_iff (weight_integrable F hm)]
  exact (weight_memLp F hm).integrable_mul hg

theorem tilted_integral_ratio {m : ℕ} (F : EdgeSet m) (g : (Fin m → ℝ) → ℝ) :
    (∫ z, g z ∂tiltedMeasure F) =
      (∫ z, weight F z*g z ∂gaussian (Fin m)) / (∫ z, weight F z ∂gaussian (Fin m)) := by
  rw [tiltedMeasure, integral_tilted]
  simp only [weight, smul_eq_mul, div_mul_eq_mul_div, integral_div]

theorem tilted_abs_bound {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m)
    {g : (Fin m → ℝ) → ℝ} (hg : MemLp g 2 (gaussian (Fin m))) :
    (∫ z, |g z| ∂tiltedMeasure F) ≤ Real.exp 4 * Real.sqrt (∫ z, (g z)^2 ∂gaussian (Fin m)) := by
  rw [tilted_integral_ratio]
  have hw := weight_integral_ge_one F hm
  have hn : 0 ≤ ∫ z, weight F z*|g z| ∂gaussian (Fin m) :=
    integral_nonneg (fun z => mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
  calc
    _ ≤ ∫ z, weight F z*|g z| ∂gaussian (Fin m) :=
      div_le_self hn hw
    _ ≤ _ := weighted_abs_bound F hm hg

theorem complete_deviation_second_le (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, (quartic m z-1/2)^2 ∂gaussian (Fin m)) ≤ 3/(m : ℝ) := by
  rw [quartic_deviation_second m hm]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : 0 < (m : ℝ) := by linarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 12*(m : ℝ)^3)).mpr
  field_simp
  nlinarith [sq_nonneg (m : ℝ)]

theorem tilted_complete_concentration {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    (∫ z, |quartic m z-1/2| ∂tiltedMeasure F) ≤ Real.exp 4 * Real.sqrt (3/(m : ℝ)) := by
  exact (tilted_abs_bound F hm ((quartic_memLp_two m).sub (memLp_const _))).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (complete_deviation_second_le m (by omega)))
      (Real.exp_pos _).le)

theorem edge_memLp_two {m : ℕ} (i j : Fin m) : MemLp (edge4 i j) 2 (gaussian (Fin m)) := by
  by_cases hij : i = j
  · subst j
    have he : edge4 i i = (0 : (Fin m → ℝ) → ℝ) := by funext z; simp
    rw [he]
    exact memLp_const 0
  · apply (memLp_two_iff_integrable_sq (by unfold edge4; fun_prop)).mpr
    simpa only [pow_two] using (edge4_same_moments i j hij).1

theorem tilted_edge_bound {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) (i j : Fin m) (hij : i ≠ j) :
    (∫ z, edge4 i j z ∂tiltedMeasure F) ≤ Real.exp 4 * Real.sqrt 1680 := by
  have h := tilted_abs_bound F hm (edge_memLp_two i j)
  have ha (z : Fin m → ℝ) : |edge4 i j z| = edge4 i j z := abs_of_nonneg (by unfold edge4; positivity)
  simp_rw [ha] at h
  have hs : (∫ z, (edge4 i j z)^2 ∂gaussian (Fin m)) = 1680 := by
    simpa only [pow_two] using (edge4_same_moments i j hij).2
  rwa [hs] at h
end ForestQuartic
