module

public import TournamentHamiltonian.RegularFourier.Parity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation UniformBlowup
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def e01 : Edge 3 := ⟨(0,1),by decide⟩
def e02 : Edge 3 := ⟨(0,2),by decide⟩
def e12 : Edge 3 := ⟨(1,2),by decide⟩
def eTwo : Edge 2 := ⟨(0,1),by decide⟩

lemma edge_univ_one : (Finset.univ : Finset (Edge 1))=∅ := by
  ext e
  rcases e with ⟨⟨i,j⟩,h⟩
  change i < j at h
  fin_cases i; fin_cases j; norm_num at h
lemma edge_univ_two : (Finset.univ : Finset (Edge 2))={eTwo} := by
  ext e
  rcases e with ⟨⟨i,j⟩,h⟩
  change i < j at h
  fin_cases i <;> fin_cases j <;> norm_num [eTwo] at * <;> (dsimp at h; omega)
lemma edge_univ_three : (Finset.univ : Finset (Edge 3))={e01,e02,e12} := by
  ext e
  rcases e with ⟨⟨i,j⟩,h⟩
  change i < j at h
  fin_cases i <;> fin_cases j <;> norm_num [e01,e02,e12] at * <;> (dsimp at h; omega)

lemma order_one_root (s : Finset (Edge 1)) (ω : Orientation 1) : rootIntegral s ω=1 := by
  unfold rootIntegral signedKernel
  rw [edge_univ_one]
  simp

lemma order_two_kernel (ω : Orientation 2) (x : Fin 2 → ℝ) :
    signedKernel ∅ ω x=(Real.cos (x 0-x 1):ℂ) := by
  simp [signedKernel,edge_univ_two,eTwo,signedFactor]

lemma cos_cell : (∫ t,Real.cos t ∂cellMeasure (-Real.pi/2))=2 := by
  rw [integral_cell,integral_cos]
  rw [show -Real.pi/2+Real.pi=Real.pi/2 by ring]
  norm_num [neg_div]
lemma sin_cell : (∫ t,Real.sin t ∂cellMeasure (-Real.pi/2))=0 := by
  rw [integral_cell,integral_sin]
  rw [show -Real.pi/2+Real.pi=Real.pi/2 by ring]
  simp [neg_div]

lemma integral_one_coordinate (f : ℝ → ℝ) :
    (∫ z : Fin 1 → ℝ,f (z 0) ∂boxMeasure 1 (-Real.pi/2))=
      ∫ t,f t ∂cellMeasure (-Real.pi/2) := by
  simpa only [Fin.prod_univ_one,boxMeasure] using
    integral_fintype_prod_eq_prod (fun (_ : Fin 1) (t : ℝ) => f t)
lemma integral_two_product (f : ℝ → ℝ) :
    (∫ z : Fin 2 → ℝ,f (z 0)*f (z 1) ∂boxMeasure 2 (-Real.pi/2))=
      (∫ t,f t ∂cellMeasure (-Real.pi/2))^2 := by
  simpa only [Fin.prod_univ_two,boxMeasure,pow_two] using
    integral_fintype_prod_eq_prod (fun (_ : Fin 2) (t : ℝ) => f t)
lemma complex_integral_ofReal {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (∫ x,(f x : ℂ) ∂μ)=(∫ x,f x ∂μ : ℝ) := integral_ofReal

/-- Even order two has nonzero signed π-cell root integral. -/
theorem order_two_root (ω : Orientation 2) : rootIntegral ∅ ω=2 := by
  unfold rootIntegral
  have he (z : Fin 1 → ℝ) : signedKernel ∅ ω (Fin.cons 0 z)=(Real.cos (z 0):ℂ) := by
    rw [order_two_kernel ω]
    simp
  simp_rw [he]
  rw [complex_integral_ofReal,integral_one_coordinate,cos_cell]
  norm_num

/-- The full signed π-box integral is 4, not π times its root integral 2. -/
theorem order_two_full (ω : Orientation 2) :
    (∫ x,signedKernel ∅ ω x ∂boxMeasure 2 (-Real.pi/2))=4 := by
  simp_rw [order_two_kernel]
  rw [complex_integral_ofReal]
  simp_rw [Real.cos_sub]
  have hc : Integrable (fun x : Fin 2 → ℝ => Real.cos (x 0)*Real.cos (x 1))
      (boxMeasure 2 (-Real.pi/2)) := by
    apply integrable_bounded _ (by fun_prop) (M:=1)
    intro x
    rw [abs_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hs : Integrable (fun x : Fin 2 → ℝ => Real.sin (x 0)*Real.sin (x 1))
      (boxMeasure 2 (-Real.pi/2)) := by
    apply integrable_bounded _ (by fun_prop) (M:=1)
    intro x
    rw [abs_mul]
    calc
      _ ≤ 1*1 := mul_le_mul (Real.abs_sin_le_one _) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  rw [integral_add hc hs,integral_two_product,integral_two_product,cos_cell,sin_cell]
  norm_num

theorem order_two_gauge_fails (ω : Orientation 2) :
    (∫ x,signedKernel ∅ ω x ∂boxMeasure 2 (-Real.pi/2))≠
      (Real.pi:ℂ)*rootIntegral ∅ ω := by
  rw [order_two_full,order_two_root]
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr
  linarith [Real.pi_gt_three]

end RegularFourier
