module

public import TournamentHamiltonian.RootGaussianTail.Base

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootGaussianTail
open Matrix MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def halfspace (n : ℕ) (i : Fin n) (d t : ℝ) : Set (Fin n → ℝ) := {x | t ≤ d*x i}
def coordinateTail (n : ℕ) (i : Fin n) (t : ℝ) : Set (Fin n → ℝ) := {x | t ≤ |x i|}
def maxTail (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) := {x | ∃ i, t ≤ |x i|}

theorem halfspace_measurable (n : ℕ) (i : Fin n) (d t : ℝ) :
    MeasurableSet (halfspace n i d t) := by
  apply (isClosed_le continuous_const (continuous_const.mul (continuous_apply i))).measurableSet

theorem coordinateTail_measurable (n : ℕ) (i : Fin n) (t : ℝ) :
    MeasurableSet (coordinateTail n i t) := by
  exact (isClosed_le continuous_const (continuous_apply i).abs).measurableSet

theorem maxTail_measurable (n : ℕ) (t : ℝ) : MeasurableSet (maxTail n t) := by
  have he : maxTail n t = ⋃ i, coordinateTail n i t := by ext x; simp [maxTail, coordinateTail]
  rw [he]
  exact MeasurableSet.iUnion (fun i => coordinateTail_measurable n i t)

/-- A pointwise exponential Markov bound, integrated against genuine Lebesgue volume. -/
theorem halfspace_chernoff (n : ℕ) (a : ℝ) (ha : 0 < a) (i : Fin n)
    (d t s : ℝ) (hs : 0 ≤ s) :
    (∫ x in halfspace n i d t, density n a x) ≤
      partition n a * Real.exp (-s*t + (s*d)^2/(a*(n+1 : ℝ))) := by
  rw [← integral_indicator (halfspace_measurable n i d t)]
  have hp (x : Fin n → ℝ) :
      (halfspace n i d t).indicator (density n a) x ≤
        Real.exp (-s*t) * tilted n a i (s*d) x := by
    by_cases hx : x ∈ halfspace n i d t
    · rw [Set.indicator_of_mem hx, density_exp, tilted, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hxt : t ≤ d*x i := hx
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hxt)]
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hi := integral_mono_ae ((density_integrable n a ha).indicator
    (halfspace_measurable n i d t)) ((tilted_integrable n a ha i (s*d)).const_mul (Real.exp (-s*t)))
    (ae_of_all _ hp)
  refine hi.trans_eq ?_
  rw [integral_const_mul, tilted_integral n a ha, mul_left_comm, ← Real.exp_add]

theorem halfspace_tail (n : ℕ) (a : ℝ) (ha : 0 < a) (i : Fin n)
    (d t : ℝ) (hd : d^2 = 1) (ht : 0 ≤ t) :
    (∫ x in halfspace n i d t, density n a x) ≤
      partition n a * Real.exp (-a*(n+1 : ℝ)*t^2/4) := by
  have h := halfspace_chernoff n a ha i d t (a*(n+1 : ℝ)*t/2) (by positivity)
  have he : -(a*(n+1 : ℝ)*t/2)*t + ((a*(n+1 : ℝ)*t/2)*d)^2/(a*(n+1 : ℝ)) =
      -a*(n+1 : ℝ)*t^2/4 := by
    have han : a*(n+1 : ℝ) ≠ 0 := by positivity
    rw [mul_pow, hd, mul_one]
    field_simp
    ring
  rwa [he] at h

/-- Nonnegative integrable weights obey a finite union bound, without a probability construction. -/
theorem weighted_union_bound {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (S : ι → Set α) (hS : ∀ i, MeasurableSet (S i)) :
    (∫ x in ⋃ i, S i, f x ∂μ) ≤ ∑ i, ∫ x in S i, f x ∂μ := by
  rw [← integral_indicator (MeasurableSet.iUnion hS)]
  have hg (i : ι) : Integrable ((S i).indicator f) μ := hf.indicator (hS i)
  have hsum : Integrable (fun x => ∑ i, (S i).indicator f x) μ := by
    exact integrable_finsetSum _ (fun i _ => hg i)
  have hp (x : α) : (⋃ i, S i).indicator f x ≤ ∑ i, (S i).indicator f x := by
    have hnon (i : ι) : 0 ≤ (S i).indicator f x := by
      by_cases hx : x ∈ S i <;> simp [hx, hf0 x]
    by_cases hx : x ∈ ⋃ i, S i
    · rw [Set.indicator_of_mem hx]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      calc
        f x = (S i).indicator f x := (Set.indicator_of_mem hi f).symm
        _ ≤ ∑ j, (S j).indicator f x := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    · rw [Set.indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun i _ => hnon i)
  have h := integral_mono_ae (hf.indicator (MeasurableSet.iUnion hS)) hsum (ae_of_all _ hp)
  rw [integral_finsetSum _ (fun i _ => hg i)] at h
  simpa only [integral_indicator (hS _)] using h

theorem coordinate_double_tail (n : ℕ) (a : ℝ) (ha : 0 < a) (i : Fin n)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in coordinateTail n i t, density n a x) ≤
      2 * partition n a * Real.exp (-a*(n+1 : ℝ)*t^2/4) := by
  let S : Bool → Set (Fin n → ℝ) := fun b => halfspace n i (if b then 1 else -1) t
  have he : coordinateTail n i t = ⋃ b, S b := by
    ext x
    simp [S, coordinateTail, halfspace, le_abs, or_comm]
  rw [he]
  have h := weighted_union_bound volume (density n a) (density_integrable n a ha)
    (density_nonneg n a) S (fun b => halfspace_measurable n i _ t)
  refine h.trans ?_
  have hh (b : Bool) : (∫ x in S b, density n a x) ≤
      partition n a * Real.exp (-a*(n+1 : ℝ)*t^2/4) :=
    halfspace_tail n a ha i _ t (by cases b <;> norm_num) ht
  calc
    (∑ b, ∫ x in S b, density n a x) ≤
        ∑ _ : Bool, partition n a * Real.exp (-a*(n+1 : ℝ)*t^2/4) :=
      Finset.sum_le_sum (fun b _ => hh b)
    _ = _ := by simp; ring

/-- Finite maximum tail, including t=0. This is an actual weighted Lebesgue integral. -/
theorem finite_max_tail (n : ℕ) (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in maxTail n t, density n a x) ≤
      2 * n * partition n a * Real.exp (-a*(n+1 : ℝ)*t^2/4) := by
  have he : maxTail n t = ⋃ i, coordinateTail n i t := by ext x; simp [maxTail, coordinateTail]
  rw [he]
  have h := weighted_union_bound volume (density n a) (density_integrable n a ha)
    (density_nonneg n a) (fun i => coordinateTail n i t) (fun i => coordinateTail_measurable n i t)
  refine h.trans ?_
  calc
    (∑ i, ∫ x in coordinateTail n i t, density n a x) ≤
        ∑ _ : Fin n, 2 * partition n a * Real.exp (-a*(n+1 : ℝ)*t^2/4) :=
      Finset.sum_le_sum (fun i _ => coordinate_double_tail n a ha i t ht)
    _ = _ := by simp; ring

theorem vertex_max_tail (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in maxTail (p-1) t, density (p-1) a x) ≤
      2 * (p-1 : ℕ) * Z p a * Real.exp (-a*p*t^2/4) := by
  have h := finite_max_tail (p-1) a ha t ht
  have he : ((p-1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ p))
  simpa only [he, Z] using h
end RootGaussianTail
