module

public import TournamentHamiltonian.PDGaussian.Forest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PDGaussian
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem empty_dimension_integral (A : Matrix (Fin 0) (Fin 0) ℝ) (z : Fin 0 → ℂ) :
    (∫ x : Fin 0 → ℝ, kernel A z x) = 1 := by
  have hA : A.PosDef := by
    have he : A = 1 := Subsingleton.elim _ _
    rw [he]
    exact Matrix.PosDef.one
  rw [kernel_integral hA]
  simp [normalization, bilinear, Matrix.det_isEmpty]

theorem empty_dimension_integrable (A : Matrix (Fin 0) (Fin 0) ℝ) (z : Fin 0 → ℂ) :
    Integrable (kernel A z) := by
  apply kernel_integrable
  have he : A = 1 := Subsingleton.elim _ _
  rw [he]
  exact Matrix.PosDef.one

theorem diagonal_inverse {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) :
    (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  have he : (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) := by
    funext i
    exact mul_inv_cancel₀ (ne_of_gt (hd i))
  rw [he, Matrix.diagonal_one]

theorem diagonal_kernel_integral {ι : Type*} [Fintype ι] (d : ι → ℝ)
    (hd : ∀ i, 0 < d i) (z : ι → ℂ) :
    (∫ x : ι → ℝ, kernel (diagonal d) z x) =
      (((Real.sqrt (2 * Real.pi))^Fintype.card ι / Real.sqrt (∏ i, d i) : ℝ) : ℂ) *
      Complex.exp ((∑ i, z i^2 / (d i : ℂ))/2) := by
  have h : (diagonal d : Matrix ι ι ℝ).PosDef := Matrix.posDef_diagonal_iff.mpr hd
  rw [kernel_integral h]
  congr 1
  · simp [normalization]
  · congr 1
    rw [bilinear, diagonal_inverse d hd]
    have he : complexify (diagonal (fun i => (d i)⁻¹)) =
        diagonal (fun i => (d i : ℂ)⁻¹) := by
      ext i j
      by_cases hij : i = j <;> simp [complexify, hij]
    rw [he]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- One real coordinate: positive MGF exponent, tested independently of forest instantiation. -/
theorem one_dimensional_MGF (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (∫ x : Fin 1 → ℝ, Real.exp (-a*(x 0)^2/2 + t*x 0)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt a * Real.exp (t^2/(2*a)) := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  have h := realKernel_integral
    (Matrix.posDef_diagonal_iff.mpr (fun _ : Fin 1 => ha)) (fun _ : Fin 1 => t)
  have hf (x : Fin 1 → ℝ) : realKernel (diagonal (fun _ : Fin 1 => a)) (fun _ => t) x =
      Real.exp (-a*(x 0)^2/2 + t*x 0) := by
    simp only [realKernel, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.diagonal_apply_eq]
    congr 1
    ring
  simp_rw [hf] at h
  have hn : normalization (diagonal (fun _ : Fin 1 => a)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt a := by
    simp only [normalization, Matrix.det_diagonal, Fin.prod_univ_one, Fintype.card_fin, pow_one]
  rw [hn] at h
  have hq : (fun _ : Fin 1 => t) ⬝ᵥ (diagonal (fun _ : Fin 1 => a))⁻¹ *ᵥ (fun _ => t) = t^2/a := by
    rw [diagonal_inverse _ (fun _ => ha)]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.diagonal_apply_eq]
    ring
  rw [hq] at h
  convert h using 1
  congr 2
  ring

/-- The phase exponent has the opposite sign: I² = -1, no conjugation. -/
theorem one_dimensional_phase (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (∫ x : Fin 1 → ℝ, Complex.exp (-(a : ℂ)*(x 0 : ℂ)^2/2 + Complex.I*t*x 0)) =
      (Real.sqrt (2 * Real.pi) / Real.sqrt a * Real.exp (-t^2/(2*a)) : ℝ) := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  have h := phaseKernel_integral
    (Matrix.posDef_diagonal_iff.mpr (fun _ : Fin 1 => ha)) (fun _ : Fin 1 => t)
  have hf (x : Fin 1 → ℝ) : phaseKernel (diagonal (fun _ : Fin 1 => a)) (fun _ => t) x =
      Complex.exp (-(a : ℂ)*(x 0 : ℂ)^2/2 + Complex.I*t*x 0) := by
    simp only [phaseKernel, dotProduct, Matrix.mulVec, Fin.sum_univ_one, Matrix.diagonal_apply_eq,
      Complex.ofReal_mul]
    congr 1
    ring
  simp_rw [hf] at h
  have hn : normalization (diagonal (fun _ : Fin 1 => a)) =
      Real.sqrt (2 * Real.pi) / Real.sqrt a := by
    simp only [normalization, Matrix.det_diagonal, Fin.prod_univ_one, Fintype.card_fin, pow_one]
  rw [hn] at h
  have hq : (fun _ : Fin 1 => t) ⬝ᵥ (diagonal (fun _ : Fin 1 => a))⁻¹ *ᵥ (fun _ => t) = t^2/a := by
    rw [diagonal_inverse _ (fun _ => ha)]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Matrix.diagonal_apply_eq]
    ring
  rw [hq] at h
  convert h using 1
  congr 3
  ring

theorem empty_forest_ratio (n : ℕ) (hm : 8 ≤ n+1) :
    (∫ x : Fin n → ℝ, phaseKernel (rootMatrix (emptyEdgeSet (n+1)))
      (rootImbalance (emptyEdgeSet (n+1))) x) /
      (∫ x : Fin n → ℝ, realKernel (rootMatrix (emptyEdgeSet (n+1))) 0 x : ℝ) = 1 := by
  rw [forest_integral_ratio _ hm, gaussianFactor_empty]
  norm_num

theorem order_eight_coordinate_MGF (t : ℝ) :
    (∫ x : Fin 7 → ℝ, Real.exp (-(x ⬝ᵥ completeRoot 7 *ᵥ x)/2 + t*x 0)) /
      (∫ x : Fin 7 → ℝ, realKernel (completeRoot 7) 0 x) = Real.exp (t^2/8) := by
  convert complete_coordinate_MGF 7 1 (by norm_num) 0 t using 1 <;> norm_num
end PDGaussian
