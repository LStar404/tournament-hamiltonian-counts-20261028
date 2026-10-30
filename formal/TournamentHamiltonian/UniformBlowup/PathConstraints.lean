module

public import TournamentHamiltonian.UniformBlowup.Model

@[expose] public section

namespace UniformBlowup
open TournamentHamiltonian
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual consecutive positions. This includes no wrap-around edge. -/
abbrev Step (n : ℕ) := {p : Fin n × Fin n // p.2.val = p.1.val + 1}
abbrev Arrangement (d m : ℕ) := Fin (d*m) ≃ Vertex d m

def tail {d m : ℕ} (π : Arrangement d m) (r : Step (d*m)) : Vertex d m := π r.val.1
def head {d m : ℕ} (π : Arrangement d m) (r : Step (d*m)) : Vertex d m := π r.val.2

theorem tail_ne_head {d m : ℕ} (π : Arrangement d m) (r : Step (d*m)) :
    tail π r ≠ head π r := by
  intro h
  have hp := congrArg Fin.val (π.injective h)
  have hr := r.property
  omega

abbrev InternalStep {d m : ℕ} (π : Arrangement d m) :=
  {r : Step (d*m) // (tail π r).1 = (head π r).1}

def internalCoord {d m : ℕ} (π : Arrangement d m) (r : InternalStep π) : Coord d m :=
  ((tail π r.val).1, edgeOf (tail π r.val).2 (head π r.val).2
    (fun h => tail_ne_head π r.val (Prod.ext r.property h)))

def internalForward {d m : ℕ} (π : Arrangement d m) (r : InternalStep π) : Bool :=
  decide ((tail π r.val).2 < (head π r.val).2)

/-- A real vertex ordering cannot use an unordered internal edge twice.
The reversed case contradicts the two successor equations, rather than being
ruled out by an independence hypothesis. -/
theorem internalCoord_injective {d m : ℕ} (π : Arrangement d m) :
    Function.Injective (internalCoord π) := by
  intro r s h
  have hb := congrArg Prod.fst h
  change (tail π r.val).1 = (tail π s.val).1 at hb
  have he := congrArg Prod.snd h
  have he' := (edgeOf_eq_iff _ _ _ _
    (fun h => tail_ne_head π r.val (Prod.ext r.property h))
    (fun h => tail_ne_head π s.val (Prod.ext s.property h))).mp he
  rcases he' with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have ht' : tail π r.val = tail π s.val := Prod.ext hb ht
    have hh' : head π r.val = head π s.val :=
      Prod.ext (r.property.symm.trans (hb.trans s.property)) hh
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (π.injective ht') (π.injective hh')
  · have ht' : tail π r.val = head π s.val := Prod.ext (hb.trans s.property) ht
    have hh' : head π r.val = tail π s.val := Prod.ext (r.property.symm.trans hb) hh
    have hp := congrArg Fin.val (π.injective ht')
    have hq := congrArg Fin.val (π.injective hh')
    have hr := r.val.property
    have hs := s.val.property
    omega

/-- The actual set of unordered internal-edge coordinates used by the path. -/
def internalEdges {d m : ℕ} (π : Arrangement d m) : Finset (Coord d m) :=
  Finset.univ.image (internalCoord π)

def b {d m : ℕ} (π : Arrangement d m) : ℕ := (internalEdges π).card

theorem b_eq_card_internalStep {d m : ℕ} (π : Arrangement d m) :
    b π = Fintype.card (InternalStep π) := by
  simp [b, internalEdges, Finset.card_image_of_injective _ (internalCoord_injective π)]

theorem b_le {d m : ℕ} (π : Arrangement d m) : b π ≤ d * m.choose 2 := by
  rw [← card_coord]
  exact Finset.card_le_univ _

/-- One total assignment extending all demanded internal directions. -/
def demand {d m : ℕ} (π : Arrangement d m) (c : Coord d m) : Bool :=
  if h : ∃ r : InternalStep π, internalCoord π r = c then
    internalForward π (Classical.choose h) else false

theorem demand_at {d m : ℕ} (π : Arrangement d m) (r : InternalStep π) :
    demand π (internalCoord π r) = internalForward π r := by
  have hx : ∃ s : InternalStep π, internalCoord π s = internalCoord π r := ⟨r, rfl⟩
  simp only [demand, dite_eq_left hx]
  rw [internalCoord_injective π (Classical.choose_spec hx)]

theorem internal_arc_iff {d m : ℕ} (T : Tournament d) (π : Arrangement d m)
    (ω : Sample d m) (r : InternalStep π) :
    arc T ω (tail π r.val) (head π r.val) = true ↔
      ω (internalCoord π r) = internalForward π r := by
  have hi : (tail π r.val).2 ≠ (head π r.val).2 :=
    fun h => tail_ne_head π r.val (Prod.ext r.property h)
  simp only [arc, r.property, ite_true, internalArc, dite_eq_right hi,
    internalCoord, internalForward]
  by_cases hl : (tail π r.val).2 < (head π r.val).2
  · simp [hl]
  · simp [hl]

/-- All deterministic cross-block arcs point in the required direction. -/
def Compatible {d m : ℕ} (T : Tournament d) (π : Arrangement d m) : Prop :=
  ∀ r : Step (d*m), (tail π r).1 ≠ (head π r).1 →
    T.val (tail π r).1 (head π r).1 = true

/-- A Hamilton path in the actual sampled blowup, with vertices listed by π. -/
def IsPath {d m : ℕ} (T : Tournament d) (ω : Sample d m) (π : Arrangement d m) : Prop :=
  ∀ r : Step (d*m), arc T ω (tail π r) (head π r) = true

/-- The complete semantic bridge from graph arcs to consistent cube coordinates. -/
theorem isPath_iff {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (π : Arrangement d m) :
    IsPath T ω π ↔ Compatible T π ∧ ∀ c ∈ internalEdges π, ω c = demand π c := by
  constructor
  · intro hp
    constructor
    · intro r hr
      simpa [arc, hr] using hp r
    · intro c hc
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hc
      rw [demand_at]
      exact (internal_arc_iff T π ω r).mp (hp r.val)
  · rintro ⟨hc, hi⟩ r
    by_cases hr : (tail π r).1 = (head π r).1
    · let q : InternalStep π := ⟨r, hr⟩
      have hq := hi (internalCoord π q) (Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩)
      rw [demand_at] at hq
      exact (internal_arc_iff T π ω q).mpr hq
    · simpa [arc, hr] using hc r hr

/-- Exact finite completion count. The exponent counts genuinely unused coordinates. -/
theorem path_completion_count {d m : ℕ} (T : Tournament d) (π : Arrangement d m) :
    (Finset.univ.filter (fun ω : Sample d m => IsPath T ω π)).card =
      if Compatible T π then 2 ^ (d * m.choose 2 - b π) else 0 := by
  classical
  simp_rw [isPath_iff]
  by_cases hc : Compatible T π
  · simp only [hc, true_and, ite_true]
    simpa only [card_coord, b] using fixed_filter_card (internalEdges π) (demand π)
  · simp [hc]

/-- Agreement with the pre-existing manuscript Hamilton-path predicate under any labelling. -/
theorem isPath_iff_existing {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) (σ : Equiv.Perm (Fin (d*m))) :
    IsPath T ω (σ.trans e) ↔ IsHamiltonian (blowup T ω e) σ := by
  constructor
  · intro h i j hij
    exact h ⟨(i,j), hij⟩
  · intro h r
    exact h r.val.1 r.val.2 r.property

end
end UniformBlowup
