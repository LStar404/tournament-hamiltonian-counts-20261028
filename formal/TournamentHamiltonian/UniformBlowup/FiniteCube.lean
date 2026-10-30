module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

/-! Exact counting of completions of prescribed Boolean coordinates.
No probability or independence assumption is used. -/
namespace UniformBlowup

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {C : Type*} [Fintype C] [DecidableEq C]

abbrev Fixed (s : Finset C) (a : C → Bool) :=
  {ω : C → Bool // ∀ c ∈ s, ω c = a c}

/-- Forget prescribed coordinates; all other bits are arbitrary. -/
def fixedEquiv (s : Finset C) (a : C → Bool) :
    Fixed s a ≃ ({c : C // c ∉ s} → Bool) where
  toFun ω c := ω.1 c.1
  invFun f := ⟨fun c => if h : c ∈ s then a c else f ⟨c, h⟩,
    by intro c hc; simp [hc]⟩
  left_inv ω := by
    apply Subtype.ext
    funext c
    by_cases hc : c ∈ s
    · simpa [hc] using (ω.2 c hc).symm
    · simp [hc]
  right_inv f := by
    funext c
    simp [c.2]

theorem fixed_card (s : Finset C) (a : C → Bool) :
    Fintype.card (Fixed s a) = 2 ^ (Fintype.card C - s.card) := by
  rw [Fintype.card_congr (fixedEquiv s a), Fintype.card_fun,
    Fintype.card_subtype_compl]
  simp

theorem fixed_filter_card (s : Finset C) (a : C → Bool) :
    (Finset.univ.filter (fun ω : C → Bool => ∀ c ∈ s, ω c = a c)).card =
      2 ^ (Fintype.card C - s.card) := by
  classical
  simpa only [Fixed, Fintype.card_subtype] using fixed_card s a

end
end UniformBlowup
