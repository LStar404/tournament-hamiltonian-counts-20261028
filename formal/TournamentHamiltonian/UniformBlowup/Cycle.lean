module

public import TournamentHamiltonian.UniformBlowup.Expectation
public import Mathlib.GroupTheory.Perm.Cycle.Basic

@[expose] public section

/-! A Hamilton cycle is a full-support single successor permutation, so it has
no distinguished start and is counted once, not `N` times. The finite probability
formula below requires `N ≥ 3`: at `N = 2` the two arcs repeat one unordered edge. -/
namespace UniformBlowup
open TournamentHamiltonian Equiv.Perm
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Cycle (d m : ℕ) :=
  {σ : Equiv.Perm (Vertex d m) // σ.IsCycle ∧ σ.support = Finset.univ}

theorem cycle_ne_self {d m : ℕ} (σ : Cycle d m) (u : Vertex d m) : σ.val u ≠ u := by
  apply Equiv.Perm.mem_support.mp
  rw [σ.property.2]
  exact Finset.mem_univ _

theorem cycle_not_two {d m : ℕ} (hN : 3 ≤ d*m) (σ : Cycle d m) (u : Vertex d m) :
    σ.val (σ.val u) ≠ u := by
  intro h
  have heq := σ.property.1.eq_swap_of_apply_apply_eq_self (cycle_ne_self σ u) h
  have hc : σ.val.support.card = 2 := by
    rw [heq]
    exact Equiv.Perm.card_support_swap (cycle_ne_self σ u).symm
  rw [σ.property.2] at hc
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hc
  omega

abbrev CycleInternal {d m : ℕ} (σ : Cycle d m) :=
  {u : Vertex d m // u.1 = (σ.val u).1}

def cycleCoord {d m : ℕ} (σ : Cycle d m) (u : CycleInternal σ) : Coord d m :=
  (u.val.1, edgeOf u.val.2 (σ.val u.val).2
    (fun h => cycle_ne_self σ u.val (Prod.ext u.property h).symm))

def cycleForward {d m : ℕ} (σ : Cycle d m) (u : CycleInternal σ) : Bool :=
  decide (u.val.2 < (σ.val u.val).2)

/-- No independent-edge assumption: full cycle structure excludes a repeated
unordered pair, because the only possible collision would be a two-cycle. -/
theorem cycleCoord_injective {d m : ℕ} (hN : 3 ≤ d*m) (σ : Cycle d m) :
    Function.Injective (cycleCoord σ) := by
  intro u v h
  have hb := congrArg Prod.fst h
  change u.val.1 = v.val.1 at hb
  have he := congrArg Prod.snd h
  have he' := (edgeOf_eq_iff _ _ _ _
    (fun h => cycle_ne_self σ u.val (Prod.ext u.property h).symm)
    (fun h => cycle_ne_self σ v.val (Prod.ext v.property h).symm)).mp he
  rcases he' with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · exact Subtype.ext (Prod.ext hb ht)
  · have ht' : u.val = σ.val v.val := Prod.ext (hb.trans v.property) ht
    have hh' : σ.val u.val = v.val := Prod.ext (u.property.symm.trans hb) hh
    exact False.elim (cycle_not_two hN σ u.val (by rw [hh', ← ht']))

def cycleEdges {d m : ℕ} (σ : Cycle d m) : Finset (Coord d m) :=
  Finset.univ.image (cycleCoord σ)

def cycleB {d m : ℕ} (σ : Cycle d m) : ℕ := (cycleEdges σ).card

theorem cycleB_eq_card_internal {d m : ℕ} (hN : 3 ≤ d*m) (σ : Cycle d m) :
    cycleB σ = Fintype.card (CycleInternal σ) := by
  simp [cycleB, cycleEdges, Finset.card_image_of_injective _ (cycleCoord_injective hN σ)]

theorem cycleB_le {d m : ℕ} (σ : Cycle d m) : cycleB σ ≤ d * m.choose 2 := by
  rw [← card_coord]
  exact Finset.card_le_univ _

def cycleDemand {d m : ℕ} (σ : Cycle d m) (c : Coord d m) : Bool :=
  if h : ∃ u : CycleInternal σ, cycleCoord σ u = c then
    cycleForward σ (Classical.choose h) else false

theorem cycleDemand_at {d m : ℕ} (hN : 3 ≤ d*m) (σ : Cycle d m) (u : CycleInternal σ) :
    cycleDemand σ (cycleCoord σ u) = cycleForward σ u := by
  have hx : ∃ v : CycleInternal σ, cycleCoord σ v = cycleCoord σ u := ⟨u, rfl⟩
  simp only [cycleDemand, dite_eq_left hx]
  rw [cycleCoord_injective hN σ (Classical.choose_spec hx)]

theorem cycle_internal_arc_iff {d m : ℕ} (T : Tournament d) (σ : Cycle d m)
    (ω : Sample d m) (u : CycleInternal σ) :
    arc T ω u.val (σ.val u.val) = true ↔ ω (cycleCoord σ u) = cycleForward σ u := by
  have hi : u.val.2 ≠ (σ.val u.val).2 :=
    fun h => cycle_ne_self σ u.val (Prod.ext u.property h).symm
  simp only [arc, ite_eq_left u.property, internalArc, dite_eq_right hi,
    cycleCoord, cycleForward]
  by_cases hl : u.val.2 < (σ.val u.val).2 <;> simp [hl]

def CycleCompatible {d m : ℕ} (T : Tournament d) (σ : Cycle d m) : Prop :=
  ∀ u : Vertex d m, u.1 ≠ (σ.val u).1 → T.val u.1 (σ.val u).1 = true

def IsCyclePresent {d m : ℕ} (T : Tournament d) (ω : Sample d m) (σ : Cycle d m) : Prop :=
  ∀ u : Vertex d m, arc T ω u (σ.val u) = true

theorem isCyclePresent_iff {d m : ℕ} (hN : 3 ≤ d*m) (T : Tournament d)
    (ω : Sample d m) (σ : Cycle d m) :
    IsCyclePresent T ω σ ↔ CycleCompatible T σ ∧
      ∀ c ∈ cycleEdges σ, ω c = cycleDemand σ c := by
  constructor
  · intro hp
    constructor
    · intro u hu
      simpa [arc, hu] using hp u
    · intro c hc
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hc
      rw [cycleDemand_at hN]
      exact (cycle_internal_arc_iff T σ ω u).mp (hp u.val)
  · rintro ⟨hc, hi⟩ u
    by_cases hu : u.1 = (σ.val u).1
    · let v : CycleInternal σ := ⟨u, hu⟩
      have hv := hi (cycleCoord σ v) (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
      rw [cycleDemand_at hN] at hv
      exact (cycle_internal_arc_iff T σ ω v).mpr hv
    · simpa [arc, hu] using hc u hu

theorem cycle_completion_count {d m : ℕ} (hN : 3 ≤ d*m) (T : Tournament d) (σ : Cycle d m) :
    (Finset.univ.filter (fun ω : Sample d m => IsCyclePresent T ω σ)).card =
      if CycleCompatible T σ then 2 ^ (d * m.choose 2 - cycleB σ) else 0 := by
  classical
  simp_rw [isCyclePresent_iff hN]
  by_cases hc : CycleCompatible T σ
  · simp only [hc, true_and, ite_true]
    simpa only [card_coord, cycleB] using fixed_filter_card (cycleEdges σ) (cycleDemand σ)
  · simp [hc]

def cycleWeight {d m : ℕ} (T : Tournament d) (σ : Cycle d m) : ℝ :=
  ∏ u : Vertex d m, weight T u (σ.val u)

def weightedCycleSum {d m : ℕ} (T : Tournament d) : ℝ :=
  ∑ σ : Cycle d m, cycleWeight T σ

def cycleCount {d m : ℕ} (T : Tournament d) (ω : Sample d m) : ℕ :=
  (Finset.univ.filter (IsCyclePresent T ω)).card

def avgCycle {d m : ℕ} (T : Tournament d) : ℝ :=
  (∑ ω : Sample d m, (cycleCount T ω : ℝ)) / Fintype.card (Sample d m)

theorem cycleWeight_eq {d m : ℕ} (hN : 3 ≤ d*m) (T : Tournament d) (σ : Cycle d m) :
    cycleWeight T σ = if CycleCompatible T σ then (1/2 : ℝ) ^ cycleB σ else 0 := by
  classical
  by_cases hc : CycleCompatible T σ
  · rw [ite_eq_left hc]
    have hf : ∀ u : Vertex d m, weight T u (σ.val u) =
        if u.1 = (σ.val u).1 then (1/2 : ℝ) else 1 := by
      intro u
      simp only [weight, ite_eq_right (cycle_ne_self σ u).symm]
      by_cases hu : u.1 = (σ.val u).1
      · simp [hu]
      · simp [hu, hc u hu]
    simp only [cycleWeight, hf]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    congr 1
    rw [cycleB_eq_card_internal hN, Fintype.card_subtype]
  · rw [ite_eq_right hc]
    obtain ⟨u, hu, ha⟩ : ∃ u : Vertex d m, u.1 ≠ (σ.val u).1 ∧
        T.val u.1 (σ.val u).1 ≠ true := by
      by_contra h
      apply hc
      intro u hu
      by_contra ha
      exact h ⟨u, hu, ha⟩
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    simp [weight, (cycle_ne_self σ u).symm, hu, ha]

theorem cycle_probability_eq_weight {d m : ℕ} (hN : 3 ≤ d*m)
    (T : Tournament d) (σ : Cycle d m) :
    ((Finset.univ.filter (fun ω : Sample d m => IsCyclePresent T ω σ)).card : ℝ) /
        Fintype.card (Sample d m) = cycleWeight T σ := by
  classical
  rw [cycle_completion_count hN, card_sample, cycleWeight_eq hN]
  split_ifs with hc
  · simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_sub_div _ _ (cycleB_le σ)
  · simp

/-- Finite uniform-block cycle expectation. The successor-permutation convention
already removes the choice of cyclic starting point. No limiting statement occurs. -/
theorem avgCycle_eq_weightedCycleSum {d m : ℕ} (hN : 3 ≤ d*m) (T : Tournament d) :
    avgCycle (m := m) T = weightedCycleSum (m := m) T := by
  classical
  unfold avgCycle weightedCycleSum
  have hp : ∀ ω : Sample d m, (cycleCount T ω : ℝ) =
      ∑ σ : Cycle d m, if IsCyclePresent T ω σ then (1 : ℝ) else 0 := by
    intro ω
    symm
    exact Finset.sum_boole _ _
  simp_rw [hp]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_boole]
  exact cycle_probability_eq_weight hN T σ

end
end UniformBlowup
