module

public import TournamentHamiltonian.RootGaussianTail.AnchorBad

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootGaussianTail
open Matrix MeasureTheory ForestGaussianIntegral PDGaussian Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem density_one_dimension (a : ℝ) (x : Fin 1 → ℝ) :
    density 1 a x = Real.exp (-a*(x 0)^2/2) := by
  rw [density_exp, Matrix.smul_mulVec, dotProduct_smul, completeRoot_quadratic]
  simp only [Fin.sum_univ_one, smul_eq_mul]
  congr 1
  ring

theorem Z_two (a : ℝ) (ha : 0 < a) : Z 2 a = Real.sqrt (2*Real.pi) / Real.sqrt a := by
  simpa using Z_exact 2 (by norm_num) a ha

theorem one_dimension_double_tail (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : Fin 1 → ℝ in {x | t ≤ |x 0|}, Real.exp (-a*(x 0)^2/2)) ≤
      2 * (Real.sqrt (2*Real.pi)/Real.sqrt a) * Real.exp (-a*t^2/2) := by
  have h := coordinate_double_tail 1 a ha 0 t ht
  have hZ : partition 1 a = Real.sqrt (2*Real.pi)/Real.sqrt a := Z_two a ha
  simp only [coordinateTail, density_one_dimension, hZ] at h
  convert h using 1
  congr 2
  ring

theorem zero_threshold_integral (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    (∫ x in maxTail n 0, density n a x) = partition n a := by
  have he : maxTail n 0 = univ := by
    ext x
    simp only [maxTail, mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨⟨0, by omega⟩, abs_nonneg _⟩
  rw [he, setIntegral_univ]
  rfl

theorem perturbation_order_eight : Z 8 (1/2) ≤ Real.exp 4 * Z 8 1 := by
  convert perturbation_normalization_loss 8 (by norm_num) using 1; norm_num

theorem deletion_zero (m : ℕ) : Z m 1 / Z m 1 = 1 := by
  exact div_self (ne_of_gt (partition_pos (m-1) 1 (by norm_num)))

theorem partition_empty_dimension (a : ℝ) (ha : 0 < a) : partition 0 a = 1 := by
  rw [partition_eq 0 a ha]
  simp [normalization]

theorem empty_max_tail (a t : ℝ) :
    (∫ x in maxTail 0 t, density 0 a x) = 0 := by
  have he : maxTail 0 t = ∅ := by ext x; simp [maxTail]
  rw [he, setIntegral_empty]

theorem anchor_reversed_interval (n : ℕ) (a : ℝ) (ha : 0 < a) (l u : ℝ) (h : u ≤ l) :
    (∫ y, anchorDensity n a y ∂anchorMeasure n l u) = 0 := by
  rw [anchor_integral n a ha, max_eq_right (sub_nonpos.mpr h), zero_mul]

theorem anchor_constant_dimension_zero (a : ℝ) (ha : 0 < a) (l u : ℝ) :
    (∫ y, anchorDensity 0 a y ∂anchorMeasure 0 l u) = max (u-l) 0 := by
  rw [anchor_integral 0 a ha, partition_empty_dimension a ha, mul_one]

theorem anchor_length_two (n : ℕ) (a : ℝ) (ha : 0 < a) :
    (∫ y, anchorDensity n a y ∂anchorMeasure n 0 2) = 2 * partition n a := by
  simpa using anchor_integral n a ha 0 2
end RootGaussianTail
