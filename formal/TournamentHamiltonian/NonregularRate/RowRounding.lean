module

public import TournamentHamiltonian.FiniteVectorOrder
public import TournamentHamiltonian.BregmanBound

@[expose] public section

set_option autoImplicit false
namespace NonregularRate
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The indicator of the first R positions in the existing finite-order API. -/
def prefixIndicator {n : ℕ} (R : ℕ) (i : Fin n) : ℝ := if i.val < R then 1 else 0

theorem prefixIndicator_sum {n R : ℕ} (hR : R ≤ n) :
    ∑ i : Fin n, prefixIndicator R i = R := by
  unfold prefixIndicator
  rw [Finset.sum_boole]
  change ((finPrefix n R).card : ℝ) = R
  rw [finPrefix_card n R hR]

theorem prefixIndicator_prefix {n r R : ℕ} (hr : r ≤ n) :
    finPrefixSum (prefixIndicator (n := n) R) r = (min r R : ℕ) := by
  unfold finPrefixSum prefixIndicator
  rw [Finset.sum_boole]
  have he : ((finPrefix n r).filter (fun i => i.val < R)) = finPrefix n (min r R) := by
    ext i
    simp [lt_min_iff]
  rw [he, finPrefix_card n (min r R) ((min_le_left r R).trans hr)]

theorem bounded_weight_prefix_le {n : ℕ} (w : Fin n → ℝ) (R : ℕ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hsum : ∑ i, w i ≤ R) :
    ∀ r ≤ n, finPrefixSum w r ≤ finPrefixSum (prefixIndicator (n := n) R) r := by
  intro r hr
  rw [prefixIndicator_prefix hr]
  have hsmall : finPrefixSum w r ≤ (r : ℝ) := by
    have h := Finset.sum_le_sum (s := finPrefix n r) (fun i _ => (hw i).2)
    simpa [finPrefixSum, finPrefix_card n r hr] using h
  have htotal : finPrefixSum w r ≤ (R : ℝ) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => (hw i).1)).trans hsum
  simpa only [Nat.cast_min] using le_min hsmall htotal

/-- Finite row rounding for a nonnegative linear functional: choose the R
largest coefficients, with no distinctness or positivity assumption on them. -/
theorem exists_round_row {n R : ℕ} (hR : R ≤ n) (w c : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hsum : ∑ i, w i ≤ R)
    (hc : ∀ i, 0 ≤ c i) :
    ∃ v : Fin n → ℝ, (∀ i, v i = 0 ∨ v i = 1) ∧
      (∑ i, v i) = R ∧ (∑ i, w i*c i) ≤ ∑ i, v i*c i := by
  obtain ⟨π, hπ⟩ := sorted_abs_exists c
  have hsort : Antitone (fun i => c (π i)) := by
    simpa only [abs_of_nonneg (hc _)] using hπ.2
  let v : Fin n → ℝ := fun j => prefixIndicator R (π.symm j)
  have hv (i : Fin n) : v (π i) = prefixIndicator R i := by simp [v]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    dsimp [v, prefixIndicator]
    split_ifs <;> simp
  · rw [← Equiv.sum_comp π v]
    simp_rw [hv]
    exact prefixIndicator_sum hR
  · have hs : ∑ i, w (π i) ≤ (R : ℝ) := by simpa only [Equiv.sum_comp π w] using hsum
    have h := finite_dot_le_of_prefix_le (fun i => w (π i)) (prefixIndicator R)
      (fun i => c (π i)) (fun i => hc (π i)) hsort
      (bounded_weight_prefix_le _ R (fun i => hw (π i)) hs)
    rw [← Equiv.sum_comp π (fun i => w i*c i), ← Equiv.sum_comp π (fun i => v i*c i)]
    simpa only [hv] using h

end
end NonregularRate
