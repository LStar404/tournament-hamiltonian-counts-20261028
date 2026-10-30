module

public import TournamentHamiltonian.UniformBlowup.FiniteCube
public import TournamentHamiltonian.Definitions

@[expose] public section

/-! The genuine uniform-block orientation cube, with no regularity assumption. -/
namespace UniformBlowup
open TournamentHamiltonian
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Vertex (d m : ℕ) := Fin d × Fin m
/-- One canonical representative for each unordered pair of distinct internal vertices. -/
abbrev Edge (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}
abbrev Coord (d m : ℕ) := Fin d × Edge m
abbrev Sample (d m : ℕ) := Coord d m → Bool

theorem card_edge (m : ℕ) : Fintype.card (Edge m) = m.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin m))

theorem card_coord (d m : ℕ) : Fintype.card (Coord d m) = d * m.choose 2 := by
  simp [card_edge]

theorem card_sample (d m : ℕ) : Fintype.card (Sample d m) = 2 ^ (d * m.choose 2) := by
  simp [card_edge]

def edgeOf {m : ℕ} (i j : Fin m) (h : i ≠ j) : Edge m :=
  ⟨(min i j, max i j), min_lt_max.mpr h⟩

theorem edgeOf_swap {m : ℕ} (i j : Fin m) (h : i ≠ j) :
    edgeOf j i h.symm = edgeOf i j h := by
  apply Subtype.ext
  simp [edgeOf, min_comm, max_comm]

/-- Equality of the canonical unordered edge means equal or swapped endpoints. -/
theorem edgeOf_eq_iff {m : ℕ} (i j k l : Fin m) (hij : i ≠ j) (hkl : k ≠ l) :
    edgeOf i j hij = edgeOf k l hkl ↔ (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    have hmin := congrArg (fun e : Edge m => e.val.1) h
    have hmax := congrArg (fun e : Edge m => e.val.2) h
    dsimp [edgeOf] at hmin hmax
    rcases lt_or_gt_of_ne hij with hij | hji <;>
      rcases lt_or_gt_of_ne hkl with hkl | hlk
    · left; simpa [min_eq_left hij.le, max_eq_right hij.le,
        min_eq_left hkl.le, max_eq_right hkl.le] using And.intro hmin hmax
    · right; simpa [min_eq_left hij.le, max_eq_right hij.le,
        min_eq_right hlk.le, max_eq_left hlk.le] using And.intro hmin hmax
    · right; simpa [min_eq_right hji.le, max_eq_left hji.le,
        min_eq_left hkl.le, max_eq_right hkl.le] using And.intro hmax hmin
    · left; simpa [min_eq_right hji.le, max_eq_left hji.le,
        min_eq_right hlk.le, max_eq_left hlk.le] using And.intro hmax hmin
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact edgeOf_swap _ _ _

/-- Smaller-to-larger orientation is the stored bit. -/
def internalArc {m : ℕ} (ω : Edge m → Bool) (i j : Fin m) : Bool :=
  if h : i = j then false else
    if i < j then ω (edgeOf i j h) else !(ω (edgeOf i j h))

@[simp] theorem internalArc_self {m : ℕ} (ω : Edge m → Bool) (i : Fin m) :
    internalArc ω i i = false := by simp [internalArc]

theorem internalArc_reverse {m : ℕ} (ω : Edge m → Bool) (i j : Fin m) (h : i ≠ j) :
    internalArc ω i j = !(internalArc ω j i) := by
  simp only [internalArc, dite_eq_right h, dite_eq_right h.symm]
  rw [edgeOf_swap i j h]
  rcases lt_or_gt_of_ne h with hij | hji
  · simp [hij, not_lt_of_ge hij.le]
  · simp [hji, not_lt_of_ge hji.le]

/-- Cross-block directions come from the actual base tournament, not from random bits. -/
def arc {d m : ℕ} (T : Tournament d) (ω : Sample d m) (u v : Vertex d m) : Bool :=
  if u.1 = v.1 then internalArc (fun e => ω (u.1, e)) u.2 v.2 else T.val u.1 v.1

@[simp] theorem arc_self {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (u : Vertex d m) : arc T ω u u = false := by simp [arc]

theorem arc_reverse {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (u v : Vertex d m) (h : u ≠ v) : arc T ω u v = !(arc T ω v u) := by
  by_cases hb : u.1 = v.1
  · have hi : u.2 ≠ v.2 := fun he => h (Prod.ext hb he)
    simp only [arc, ite_eq_left hb, ite_eq_left hb.symm]
    rw [← hb]
    exact internalArc_reverse _ _ _ hi
  · simpa [arc, hb, Ne.symm hb] using T.property.2 u.1 v.1 hb

/-- Relabelling onto `Fin (d*m)` yields the existing manuscript tournament type. -/
def blowup {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Fin (d*m) ≃ Vertex d m) : Tournament (d*m) :=
  ⟨fun i j => arc T ω (e i) (e j),
    ⟨fun i => arc_self T ω (e i),
     fun i j hij => arc_reverse T ω (e i) (e j) (e.injective.ne hij)⟩⟩

end
end UniformBlowup
