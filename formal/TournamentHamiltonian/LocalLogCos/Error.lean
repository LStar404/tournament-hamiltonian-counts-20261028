module

public import TournamentHamiltonian.LocalLogCos.Product

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LocalLogCos
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral ForestQuartic RootObservable PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

def errorBudget (m : ℕ) (r : ℝ) : ℝ := 32*(m : ℝ)^2*r^6

theorem retained_sixth_sum_le (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r)
    {x : Fin n → ℝ} (hx : rootBox r x) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j ∧ ¬(graph F).Adj i j),
      |rootLift x i-rootLift x j|^6) ≤ errorBudget (n+1) r := by
  let g := fun i j : Fin (n+1) => if ¬(graph F).Adj i j then |rootLift x i-rootLift x j|^6 else 0
  have hs := ordered_eq_twice_upper g
    (fun i j => by simp only [g, (graph F).adj_comm i j, abs_sub_comm])
    (fun i => by simp [g])
  have hb : (∑ i, ∑ j, g i j) ≤ (n+1 : ℝ)^2*(2*r)^6 := by
    calc
      _ ≤ ∑ _i : Fin (n+1), ∑ _j : Fin (n+1), (2*r)^6 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases ha : (graph F).Adj i j
        · simp only [g, ha, not_true_eq_false, ite_false]
          positivity
        · simpa only [g, ha, not_false_eq_true, ite_true] using
            pow_le_pow_left₀ (abs_nonneg _) (root_difference_le hr hx i j) 6
      _ = _ := by simp; ring
  have he : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j), g i j) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j ∧ ¬(graph F).Adj i j),
        |rootLift x i-rootLift x j|^6 := by
    simp only [g, Finset.sum_filter, ite_and]
  rw [he] at hs
  unfold errorBudget
  push_cast
  nlinarith

theorem remainderSum_bounds (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox r x) :
    -errorBudget (n+1) r ≤ remainderSum F x ∧ remainderSum F x ≤ 0 := by
  have hl : (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j ∧ ¬(graph F).Adj i j),
      -|rootLift x i-rootLift x j|^6) ≤ remainderSum F x := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact (remainder_bounds (root_difference_quarter hr hrp hx i j)).1
  simp only [Finset.sum_neg_distrib] at hl
  constructor
  · exact (neg_le_neg (retained_sixth_sum_le F hr hx)).trans hl
  · apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    exact (remainder_bounds (root_difference_quarter hr hrp hx i j)).2

/-- Absolute error against Gaussian times quartic correction, with no product proxy premise. -/
theorem cosProduct_error (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox r x) :
    |cosProduct F x-realKernel (rootMatrix F) 0 x * Real.exp (-rootQuartic F x)| ≤
      errorBudget (n+1) r * realKernel (rootMatrix F) 0 x := by
  have hb := remainderSum_bounds F hr hrp hx
  have he : |Real.exp (remainderSum F x)-1| ≤ -remainderSum F x := by
    have h := GaussianQuartic.exp_neg_lipschitz (neg_nonneg.mpr hb.2) (by norm_num : (0:ℝ)≤0)
    simpa only [neg_neg, neg_zero, Real.exp_zero, sub_zero, abs_of_nonneg (neg_nonneg.mpr hb.2)] using h
  have hq : Real.exp (-rootQuartic F x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rootQuartic_nonneg F x))
  have hk : 0 ≤ realKernel (rootMatrix F) 0 x := Real.exp_nonneg _
  have hex : cosProduct F x = realKernel (rootMatrix F) 0 x * Real.exp (-rootQuartic F x) * Real.exp (remainderSum F x) := by
    rw [cosProduct_expansion F hr hrp hx]
    simp only [realKernel, zero_dotProduct, add_zero, sub_eq_add_neg, Real.exp_add]
  rw [hex]
  have hid : realKernel (rootMatrix F) 0 x * Real.exp (-rootQuartic F x) * Real.exp (remainderSum F x) -
      realKernel (rootMatrix F) 0 x * Real.exp (-rootQuartic F x) =
      (realKernel (rootMatrix F) 0 x * Real.exp (-rootQuartic F x))*(Real.exp (remainderSum F x)-1) := by ring
  rw [hid, abs_mul, abs_of_nonneg (mul_nonneg hk (Real.exp_nonneg _))]
  calc
    _ ≤ (realKernel (rootMatrix F) 0 x * Real.exp (-rootQuartic F x))*(-remainderSum F x) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hk (Real.exp_nonneg _))
    _ ≤ (realKernel (rootMatrix F) 0 x)*(-remainderSum F x) := by
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hk hq) (neg_nonneg.mpr hb.2)
    _ ≤ _ := by nlinarith

/-- A unit complex phase costs no additional factor in the local error. -/
theorem unit_phase_error (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox r x) (u : ℂ) (hu : ‖u‖=1) :
    ‖u*(cosProduct F x : ℂ)-u*(realKernel (rootMatrix F) 0 x * Real.exp (-rootQuartic F x) : ℝ)‖ ≤
      errorBudget (n+1) r * realKernel (rootMatrix F) 0 x := by
  rw [← mul_sub, norm_mul, hu, one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact cosProduct_error F hr hrp hx

def phasedProduct (F : EdgeSet (n+1)) (x : Fin n → ℝ) : ℂ :=
  Complex.exp ((rootImbalance F ⬝ᵥ x : ℝ)*Complex.I)*(cosProduct F x : ℂ)

/-- Exact compatibility with the upper-pair product in the original Fourier kernel. -/
theorem cosProduct_complex_upper_if (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    (cosProduct F x : ℂ) = ∏ i, ∏ j,
      if i<j ∧ ¬(graph F).Adj i j then (Real.cos (rootLift x i-rootLift x j) : ℂ) else 1 := by
  change Complex.ofRealHom (∏ i, ∏ j ∈ Finset.univ.filter
    (fun j => i<j ∧ ¬(graph F).Adj i j), Real.cos (rootLift x i-rootLift x j)) = _
  simp only [map_prod, Finset.prod_filter, apply_ite, map_one, Complex.ofRealHom_eq_coe]

/-- The actual imbalance phase has norm one and the correct positive Fourier sign. -/
theorem actual_phase_error (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox r x) :
    ‖phasedProduct F x - phaseKernel (rootMatrix F) (rootImbalance F) x *
      (Real.exp (-rootQuartic F x) : ℂ)‖ ≤
      errorBudget (n+1) r * realKernel (rootMatrix F) 0 x := by
  have h := unit_phase_error F hr hrp hx
    (Complex.exp ((rootImbalance F ⬝ᵥ x : ℝ)*Complex.I)) (Complex.norm_exp_ofReal_mul_I _)
  have he : phaseKernel (rootMatrix F) (rootImbalance F) x =
      Complex.exp ((rootImbalance F ⬝ᵥ x : ℝ)*Complex.I)*(realKernel (rootMatrix F) 0 x : ℝ) := by
    simp only [phaseKernel, realKernel, zero_dotProduct, add_zero, Complex.ofReal_exp,
      Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.exp_add]
    simp only [mul_comm]
  rw [he, phasedProduct]
  simpa only [Complex.ofReal_mul, mul_assoc] using h


theorem cosProduct_nonneg (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox r x) : 0 ≤ cosProduct F x := by
  rw [cosProduct_expansion F hr hrp hx]
  exact Real.exp_nonneg _

/-- Actual pointwise Gaussian domination on the local root box. -/
theorem cosProduct_le_gaussian (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox r x) : cosProduct F x ≤ realKernel (rootMatrix F) 0 x := by
  rw [cosProduct_expansion F hr hrp hx, realKernel, zero_dotProduct, add_zero]
  apply Real.exp_le_exp.mpr
  have h := (remainderSum_bounds F hr hrp hx).2
  have hq := rootQuartic_nonneg F x
  linarith

theorem phasedProduct_norm_le_gaussian (F : EdgeSet (n+1)) {r : ℝ} (hr : 0 ≤ r) (hrp : r ≤ Real.pi/8)
    {x : Fin n → ℝ} (hx : rootBox r x) : ‖phasedProduct F x‖ ≤ realKernel (rootMatrix F) 0 x := by
  rw [phasedProduct, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cosProduct_nonneg F hr hrp hx)]
  exact cosProduct_le_gaussian F hr hrp hx
end LocalLogCos
