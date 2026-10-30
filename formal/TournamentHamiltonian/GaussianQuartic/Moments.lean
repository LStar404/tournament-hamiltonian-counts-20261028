module

public import TournamentHamiltonian.GaussianQuartic.Sums
public import Mathlib.Probability.Moments.Variance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
namespace GaussianQuartic
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

def unorderedSum (m : ℕ) (z : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), edge4 i j z

theorem orderedSum_eq_twice_unordered (m : ℕ) (z : Fin m → ℝ) :
    orderedSum z = 2 * unorderedSum m z := by
  have hp (i j : Fin m) : edge4 i j z =
      (if i < j then edge4 i j z else 0) + (if j < i then edge4 i j z else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp
    · simp [h, not_lt_of_gt h]
  have hrev : (∑ i : Fin m, ∑ j : Fin m, if j < i then edge4 i j z else 0) =
      ∑ i : Fin m, ∑ j : Fin m, if i < j then edge4 i j z else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [edge4_symm j i]
  calc
    orderedSum z = ∑ i, ∑ j,
        ((if i < j then edge4 i j z else 0) + (if j < i then edge4 i j z else 0)) := by
      unfold orderedSum
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hp i j))
    _ = 2 * unorderedSum m z := by
      simp_rw [Finset.sum_add_distrib]
      rw [hrev]
      simp only [unorderedSum, Finset.sum_filter]
      ring

/-- The actual quartic correction, with each unordered edge counted exactly once. -/
def quartic (m : ℕ) (z : Fin m → ℝ) : ℝ := unorderedSum m z / (12 * (m : ℝ) ^ 2)

theorem quartic_eq_ordered (m : ℕ) (z : Fin m → ℝ) :
    quartic m z = orderedSum z / (24 * (m : ℝ) ^ 2) := by
  rw [orderedSum_eq_twice_unordered]
  unfold quartic
  ring

theorem quartic_nonneg (m : ℕ) (z : Fin m → ℝ) : 0 ≤ quartic m z := by
  rw [quartic_eq_ordered]
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => by unfold edge4; positivity))
  · positivity

theorem quartic_integrable (m : ℕ) : Integrable (quartic m) (gaussian (Fin m)) := by
  have h : quartic m = fun z => orderedSum z / (24 * (m : ℝ) ^ 2) := funext (quartic_eq_ordered m)
  rw [h]
  exact orderedSum_integrable.div_const _

theorem quartic_sq_integrable (m : ℕ) :
    Integrable (fun z => quartic m z ^ 2) (gaussian (Fin m)) := by
  simp_rw [quartic_eq_ordered, div_pow]
  exact orderedSum_sq_integrable.div_const _

theorem quartic_mean (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, quartic m z ∂gaussian (Fin m)) = ((m : ℝ) - 1) / (2 * m) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp_rw [quartic_eq_ordered]
  rw [integral_div, orderedSum_integral]
  simp only [Fintype.card_fin]
  field_simp
  ring

theorem quartic_second_moment (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, quartic m z ^ 2 ∂gaussian (Fin m)) =
      ((m : ℝ) - 1) * (6 * (m : ℝ)^2 + 46 * m + 24) / (24 * (m : ℝ)^3) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp_rw [quartic_eq_ordered, div_pow]
  rw [integral_div, orderedSum_sq_integral]
  simp only [Fintype.card_fin]
  field_simp
  ring

theorem quartic_memLp_two (m : ℕ) : MemLp (quartic m) 2 (gaussian (Fin m)) :=
  (memLp_two_iff_integrable_sq (quartic_integrable m).aestronglyMeasurable).2
    (quartic_sq_integrable m)

theorem quartic_variance (m : ℕ) (hm : 1 ≤ m) :
    variance (quartic m) (gaussian (Fin m)) =
      ((m : ℝ) - 1) * (13 * m + 6) / (6 * (m : ℝ)^3) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [variance_eq_sub (quartic_memLp_two m)]
  change (∫ z, quartic m z ^ 2 ∂gaussian (Fin m)) -
    (∫ z, quartic m z ∂gaussian (Fin m)) ^ 2 = _
  rw [quartic_second_moment m hm, quartic_mean m hm]
  field_simp
  ring

theorem quartic_centered_second (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, (quartic m z - ((m : ℝ) - 1) / (2 * m)) ^ 2 ∂gaussian (Fin m)) =
      ((m : ℝ) - 1) * (13 * m + 6) / (6 * (m : ℝ)^3) := by
  rw [← quartic_mean m hm, ← variance_eq_integral (quartic_memLp_two m).aemeasurable]
  exact quartic_variance m hm

theorem quartic_deviation_second (m : ℕ) (hm : 1 ≤ m) :
    (∫ z, (quartic m z - 1/2) ^ 2 ∂gaussian (Fin m)) =
      (26 * (m : ℝ)^2 - 11 * m - 12) / (12 * (m : ℝ)^3) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have heq : (fun z => (quartic m z - 1/2) ^ 2) =
      (fun z => quartic m z ^ 2 - quartic m z + 1/4) := by funext z; ring
  rw [heq, integral_add (f := fun z => quartic m z ^ 2 - quartic m z)
    (g := fun _ => (1/4 : ℝ))
    ((quartic_sq_integrable m).sub (quartic_integrable m)) (integrable_const _),
    integral_sub (quartic_sq_integrable m) (quartic_integrable m),
    quartic_second_moment m hm, quartic_mean m hm]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  field_simp
  ring

end
end GaussianQuartic
