module

public import TournamentHamiltonian.RootGaussianTail.DimensionRatio
public import TournamentHamiltonian.RootGaussianTail.Coordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootGaussianTail
open Matrix MeasureTheory Set PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Root-free coordinates translated by the actual anchor value. -/
def anchorDensity (n : ℕ) (a : ℝ) (y : ℝ × (Fin n → ℝ)) : ℝ :=
  density n a (fun i => y.2 i-y.1)

def anchorMeasure (n : ℕ) (l u : ℝ) : Measure (ℝ × (Fin n → ℝ)) :=
  (volume.restrict (Icc l u)).prod volume

theorem pairEnergy_sub_const (p : ℕ) (x : Fin p → ℝ) (t : ℝ) :
    pairEnergy p (fun i => x i-t) = pairEnergy p x := by
  unfold pairEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- The shifted density is exactly the complete-pair kernel at the unfixed anchor. -/
theorem anchorDensity_pair_energy (n : ℕ) (a t : ℝ) (x : Fin n → ℝ) :
    anchorDensity n a (t,x) = Real.exp (-a * pairEnergy (n+1) (Fin.cons t x)/2) := by
  rw [anchorDensity, density_pair_energy]
  have he : (Fin.cons (0 : ℝ) (fun i => x i-t) : Fin (n+1) → ℝ) = fun j => (Fin.cons t x : Fin (n+1) → ℝ) j-t := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  rw [he, pairEnergy_sub_const]

theorem anchorDensity_continuous (n : ℕ) (a : ℝ) : Continuous (anchorDensity n a) := by
  unfold anchorDensity density realKernel Matrix.mulVec dotProduct
  fun_prop

theorem translated_integrable (n : ℕ) (a : ℝ) (ha : 0 < a) (t : ℝ) :
    Integrable (fun x : Fin n → ℝ => density n a (fun i => x i-t)) :=
  (density_integrable n a ha).comp_sub_right (fun _ => t)

theorem translated_integral (n : ℕ) (a t : ℝ) :
    (∫ x : Fin n → ℝ, density n a (fun i => x i-t)) = partition n a :=
  integral_sub_right_eq_self (density n a) (fun _ => t)

theorem anchor_integrable (n : ℕ) (a : ℝ) (ha : 0 < a) (l u : ℝ) :
    Integrable (anchorDensity n a) (anchorMeasure n l u) := by
  rw [anchorMeasure, integrable_prod_iff (anchorDensity_continuous n a).aestronglyMeasurable]
  constructor
  · exact ae_of_all _ (fun t => translated_integrable n a ha t)
  · have he (t : ℝ) : (∫ x : Fin n → ℝ, ‖anchorDensity n a (t,x)‖) = partition n a := by
      simp only [anchorDensity, Real.norm_eq_abs, abs_of_nonneg (density_nonneg n a _)]
      exact translated_integral n a t
    simp_rw [he]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

/-- Exact anchor Fubini factor. The only extra factor is the interval length. -/
theorem anchor_integral (n : ℕ) (a : ℝ) (ha : 0 < a) (l u : ℝ) :
    (∫ y, anchorDensity n a y ∂anchorMeasure n l u) = max (u-l) 0 * partition n a := by
  rw [anchorMeasure, integral_prod _ (anchor_integrable n a ha l u)]
  simp only [anchorDensity, translated_integral]
  rw [setIntegral_const, Real.volume_real_Icc, smul_eq_mul]

/-- Restricting the remaining coordinates or imposing any additional box conditions can only decrease it. -/
theorem anchor_box_bound (n : ℕ) (a : ℝ) (ha : 0 < a) (l u : ℝ)
    (E : Set (ℝ × (Fin n → ℝ))) :
    (∫ y in E, anchorDensity n a y ∂anchorMeasure n l u) ≤ max (u-l) 0 * partition n a := by
  have h := setIntegral_le_integral (s := E) (anchor_integrable n a ha l u)
    (ae_of_all _ (fun y => density_nonneg n a (fun i => y.2 i-y.1)))
  exact h.trans_eq (anchor_integral n a ha l u)

theorem vertex_anchor_box_bound (p : ℕ) (a : ℝ) (ha : 0 < a) (l u : ℝ) (hlu : l ≤ u)
    (E : Set (ℝ × (Fin (p-1) → ℝ))) :
    (∫ y in E, anchorDensity (p-1) a y ∂anchorMeasure (p-1) l u) ≤ (u-l) * Z p a := by
  simpa only [max_eq_left (sub_nonneg.mpr hlu), Z] using anchor_box_bound (p-1) a ha l u E
end RootGaussianTail
