module

public import TournamentHamiltonian.NonregularDecay.Variance

@[expose] public section

set_option autoImplicit false

namespace NonregularDecay
open TournamentHamiltonian UniformBlowup
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Forgetting the single-cycle property, then relabelling, embeds each genuine
present cycle into the adjacency matrix's supported permutations. -/
def cycleToMatching {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) :
    {σ : Cycle d m // IsCyclePresent T ω σ} → SupportedMatchings (blowup T ω e).val :=
  fun σ => ⟨(e.trans σ.val.val).trans e.symm, by
    intro i
    simpa [blowup] using σ.property (e i)⟩

theorem cycleToMatching_injective {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) : Function.Injective (cycleToMatching T ω e) := by
  intro σ τ h
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro u
  have hh := congrArg (fun x : SupportedMatchings (blowup T ω e).val =>
    e (x.val (e.symm u))) h
  simpa [cycleToMatching] using hh

/-- A count of genuine full-support single cycles, not a cycle-cover surrogate. -/
theorem cycleCount_le_permanent {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) :
    (cycleCount T ω : ℝ) ≤ (adjacency (blowup T ω e)).permanent := by
  have h := Fintype.card_le_of_injective (cycleToMatching T ω e)
    (cycleToMatching_injective T ω e)
  have hR : (Fintype.card {σ : Cycle d m // IsCyclePresent T ω σ} : ℝ) ≤
      Fintype.card (SupportedMatchings (blowup T ω e).val) := by exact_mod_cast h
  rw [matching_card_eq_permanent] at hR
  convert hR using 1
  · rw [Fintype.card_subtype]
    rfl
  · rfl

/-- The manuscript cycle normalization counts each directed cycle once. -/
def meanCycles (n : ℕ) : ℝ := ((n-1).factorial : ℝ) / (2 : ℝ)^n

theorem factorial_normalization_eq (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) / (2 : ℝ)^n = (n : ℝ) * meanCycles n := by
  have hf : n.factorial = n * (n-1).factorial := (Nat.mul_factorial_pred (by omega : n ≠ 0)).symm
  rw [hf, Nat.cast_mul, meanCycles]
  ring

theorem meanCycles_pos (n : ℕ) : 0 < meanCycles n := by
  unfold meanCycles
  positivity

end
end NonregularDecay
