module

public import TournamentHamiltonian.ForestQuartic.Transfer

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ForestQuartic
open MeasureTheory GaussianQuartic ForestGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Actual quartic sum over unordered pairs not deleted by F. -/
def forestQuartic {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j ∧ ¬ (graph F).Adj i j), edge4 i j z)/(12*(m : ℝ)^2)

def removedQuartic {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) : ℝ :=
  (∑ e ∈ F.edges, edge4 e.1 e.2 z)/(12*(m : ℝ)^2)

theorem ordered_eq_twice_upper {m : ℕ} (f : Fin m → Fin m → ℝ)
    (hs : ∀ i j, f i j = f j i) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2*(∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j) := by
  have hp (i j : Fin m) : f i j = (if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp [hd]
    · simp [h, not_lt_of_gt h]
  have hr : (∑ i, ∑ j, if j < i then f i j else 0) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  calc
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j, ((if i < j then f i j else 0)+(if j < i then f i j else 0)) :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hp i j))
    _ = _ := by simp_rw [Finset.sum_add_distrib]; rw [hr]; simp only [Finset.sum_filter]; ring

theorem arc_sum_eq_upper {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) :
    (∑ e ∈ F.edges, edge4 e.1 e.2 z) =
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), if (graph F).Adj i j then edge4 i j z else 0 := by
  have ha : (∑ e ∈ F.edges, edge4 e.1 e.2 z) =
      ∑ i, ∑ j, if (i,j) ∈ F.edges then edge4 i j z else 0 := by
    rw [← Fintype.sum_prod_type (fun e : Fin m × Fin m => if e ∈ F.edges then edge4 e.1 e.2 z else 0)]
    simp
  have hp (i j : Fin m) : (if (graph F).Adj i j then edge4 i j z else 0) =
      (if (i,j) ∈ F.edges then edge4 i j z else 0) +
      (if (j,i) ∈ F.edges then edge4 i j z else 0) := by
    by_cases h : (i,j) ∈ F.edges
    · simp [graph, h, F.no_reverse i j h]
    · simp [graph, h]
  have hr : (∑ i, ∑ j, if (j,i) ∈ F.edges then edge4 i j z else 0) =
      ∑ i, ∑ j, if (i,j) ∈ F.edges then edge4 i j z else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [edge4_symm j i]
  have hs := ordered_eq_twice_upper (fun i j => if (graph F).Adj i j then edge4 i j z else 0)
    (fun i j => by simp only [(graph F).adj_comm i j, edge4_symm i j]) (fun i => by simp)
  simp_rw [hp, Finset.sum_add_distrib] at hs
  rw [hr] at hs
  rw [ha]
  simp_rw [hp, Finset.sum_add_distrib]
  linarith

theorem forest_add_removed {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) :
    forestQuartic F z + removedQuartic F z = quartic m z := by
  unfold forestQuartic removedQuartic quartic unorderedSum
  rw [arc_sum_eq_upper, ← add_div]
  congr 1
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j <;> by_cases ha : (graph F).Adj i j <;> simp [h, ha]

theorem forestQuartic_nonneg {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) : 0 ≤ forestQuartic F z := by
  unfold forestQuartic edge4
  positivity

theorem removedQuartic_nonneg {m : ℕ} (F : EdgeSet m) (z : Fin m → ℝ) : 0 ≤ removedQuartic F z := by
  unfold removedQuartic edge4
  positivity

theorem removed_memLp {m : ℕ} (F : EdgeSet m) : MemLp (removedQuartic F) 2 (gaussian (Fin m)) := by
  have h := memLp_finsetSum F.edges (fun e _ => edge_memLp_two e.1 e.2)
  change MemLp (fun z => (∑ e ∈ F.edges, edge4 e.1 e.2 z)/(12*(m : ℝ)^2)) 2 (gaussian (Fin m))
  convert h.const_mul (12*(m : ℝ)^2)⁻¹ using 1
  funext z
  ring

theorem forest_memLp {m : ℕ} (F : EdgeSet m) : MemLp (forestQuartic F) 2 (gaussian (Fin m)) := by
  have he : forestQuartic F = fun z => quartic m z-removedQuartic F z := by
    funext z
    have h := forest_add_removed F z
    linarith
  rw [he]
  exact (quartic_memLp_two m).sub (removed_memLp F)

theorem removed_tilt_integrable {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    Integrable (removedQuartic F) (tiltedMeasure F) := memLp_tilt_integrable F hm (removed_memLp F)

theorem forest_tilt_integrable {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    Integrable (forestQuartic F) (tiltedMeasure F) := memLp_tilt_integrable F hm (forest_memLp F)

theorem removed_tilt_bound {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    (∫ z, removedQuartic F z ∂tiltedMeasure F) ≤ Real.exp 4 * Real.sqrt 1680/(12*(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold removedQuartic
  rw [integral_div, integral_finsetSum _ (fun e _ => memLp_tilt_integrable F hm (edge_memLp_two e.1 e.2))]
  calc
    _ ≤ (∑ _e ∈ F.edges, Real.exp 4*Real.sqrt 1680)/(12*(m : ℝ)^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro e he
      apply tilted_edge_bound F hm
      intro hij
      have he' : (e.1,e.2) ∈ F.edges := he
      rw [← hij] at he'
      exact F.loopless e.1 he'
    _ = (F.edges.card : ℝ)*(Real.exp 4*Real.sqrt 1680)/(12*(m : ℝ)^2) := by simp
    _ ≤ (m : ℝ)*(Real.exp 4*Real.sqrt 1680)/(12*(m : ℝ)^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast edgeCount_le F
    _ = _ := by field_simp

theorem forest_complete_L1 {m : ℕ} (F : EdgeSet m) (hm : 16 ≤ m) :
    (∫ z, |forestQuartic F z-quartic m z| ∂tiltedMeasure F) ≤
      Real.exp 4 * Real.sqrt 1680/(12*(m : ℝ)) := by
  have he (z : Fin m → ℝ) : |forestQuartic F z-quartic m z| = removedQuartic F z := by
    have h := forest_add_removed F z
    have hn := removedQuartic_nonneg F z
    rw [abs_of_nonpos (by linarith)]
    linarith
  simp_rw [he]
  exact removed_tilt_bound F hm
end ForestQuartic
