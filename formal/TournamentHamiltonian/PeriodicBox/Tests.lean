module

public import TournamentHamiltonian.PeriodicBox.Local
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

set_option autoImplicit false
namespace PeriodicBox.Tests
noncomputable section
open MeasureTheory Set TorusCluster

/-- The unnormalized one-dimensional cosine test evaluates to 2, not 2/π. -/
theorem one_dim_abs_cos :
    (∫ x, |Real.cos x| ∂cellMeasure (-Real.pi/2)) = 2 := by
  rw [integral_cell, show -Real.pi/2 + Real.pi = Real.pi/2 by ring]
  calc
    (∫ x in -Real.pi/2..Real.pi/2, |Real.cos x|) =
        ∫ x in -Real.pi/2..Real.pi/2, Real.cos x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by linarith [Real.pi_pos])] at hx
      exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc (by simpa only [neg_div] using hx))
    _ = 2 := by rw [integral_cos]; norm_num [neg_div]

/-- Nonconstant one-dimensional periodic-shift test. -/
theorem one_dim_shift (a c : ℝ) :
    (∫ x, |Real.cos (x+c)| ∂cellMeasure a) = ∫ x, |Real.cos x| ∂cellMeasure a := by
  apply integral_periodic_shift a c (f := fun x => |Real.cos x|)
  intro x
  simp only [Real.cos_add_pi, abs_neg]

/-- The m=1 gauge really multiplies the 0-dimensional mass 1 by π. -/
theorem one_vertex_constant_gauge (a : ℝ) :
    (∫ _x : Fin 1 → ℝ, (1:ℝ) ∂boxMeasure 1 a) =
      Real.pi * ∫ _z : Fin 0 → ℝ, (1:ℝ) ∂boxMeasure 0 a := by
  exact gauge_root_zero (n := 0) a (fun _ => 1) measurable_const
    (M := 1) (by simp) (by intro x i; rfl) (by intro x c; rfl)

theorem one_vertex_full_mass (a : ℝ) :
    (∫ _x : Fin 1 → ℝ, (1:ℝ) ∂boxMeasure 1 a) = Real.pi := by
  simp

theorem zero_vertex_root_mass (a : ℝ) :
    (∫ _x : Fin 0 → ℝ, (1:ℝ) ∂boxMeasure 0 a) = 1 := by
  simp

/-- Constant integrands expose a missing π factor in every dimension. -/
theorem constant_gauge (n : ℕ) (a : ℝ) :
    (∫ _x : Fin (n+1) → ℝ, (1:ℝ) ∂boxMeasure (n+1) a) =
      Real.pi * ∫ _z : Fin n → ℝ, (1:ℝ) ∂boxMeasure n a := by
  exact gauge_root_zero a (fun _ => 1) measurable_const
    (M := 1) (by simp) (by intro x i; rfl) (by intro x c; rfl)

/-- For m=1 the actual root-distance bad event is empty at nonnegative t. -/
theorem one_vertex_bad_zero (H : SimpleGraph (Fin 1)) (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, badKernel H 0 t x ∂boxMeasure 1 a) = 0 := by
  have hb (x : Fin 1 → ℝ) : x ∉ rootBad 0 t := by
    intro hx
    obtain ⟨i, hi⟩ := hx
    have hi0 : i=0 := Fin.eq_zero i
    simp [hi0, circleDist, not_lt_of_ge ht] at hi
  simp [badKernel, hb]

/-- Concrete two-angle retained-edge graph: the generic bridge has no hidden
forest-degree or spectral premises, and t=0 is admitted. -/
example :
    (∫ x, badKernel (⊥ : SimpleGraph (Fin 2)) 0 0 x ∂boxMeasure 2 (-Real.pi/2)) =
      Real.pi * ∫ z, (realBad 0).indicator
        (fun z => kernel (⊥ : SimpleGraph (Fin 2)) (Fin.cons 0 z)) z
        ∂boxMeasure 1 (-Real.pi/2) :=
  cosine_gauge_real (⊥ : SimpleGraph (Fin 2)) (by norm_num)

end
end PeriodicBox.Tests

#print PeriodicBox.boxMeasure
#print PeriodicBox.CoordPeriodic
#print PeriodicBox.JointInvariant
#print PeriodicBox.rootBad
#print PeriodicBox.badKernel
#print PeriodicBox.mixedMeasure
#check PeriodicBox.integral_shift
#check PeriodicBox.integral_boxes_eq
#check PeriodicBox.gauge_root_zero
#check PeriodicBox.cosine_gauge_real
#check PeriodicBox.unwrap_arc_integral
#check PeriodicBox.unwrap_badKernel
#check PeriodicBox.unwrap_sixteen_local_badKernel
#print axioms PeriodicBox.integral_shift
#print axioms PeriodicBox.integral_boxes_eq
#print axioms PeriodicBox.gauge_root_zero
#print axioms PeriodicBox.integral_reindex
#print axioms PeriodicBox.cosine_gauge_real
#print axioms PeriodicBox.unwrap_arc_integral
#print axioms PeriodicBox.unwrap_badKernel
#print axioms PeriodicBox.unwrap_sixteen_local_badKernel
#print axioms PeriodicBox.Tests.one_dim_abs_cos
#print axioms PeriodicBox.Tests.one_dim_shift
#print axioms PeriodicBox.Tests.one_vertex_constant_gauge
#print axioms PeriodicBox.Tests.constant_gauge
#print axioms PeriodicBox.Tests.one_vertex_bad_zero

#check PeriodicBox.cosine_gauge_closed_volume
#check PeriodicBox.cosine_fixed_center_boxes
#print axioms PeriodicBox.cosine_gauge_closed_volume
#print axioms PeriodicBox.arcEvent_univ_iff_no_outliers
