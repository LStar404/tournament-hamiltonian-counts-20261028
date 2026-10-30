module

public import TournamentHamiltonian.UniformBlowup.BlockDistribution
public import Mathlib.Algebra.MvPolynomial.Basic
public import TournamentHamiltonian.Carousel

@[expose] public section

set_option autoImplicit false

namespace RegularOrientation
open TournamentHamiltonian UniformBlowup
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Orientation (m : ℕ) := Edge m → Bool
abbrev Exponent (m : ℕ) := Fin m →₀ ℕ

def winner {m : ℕ} (ω : Orientation m) (e : Edge m) : Fin m :=
  if ω e then e.val.1 else e.val.2

def loser {m : ℕ} (ω : Orientation m) (e : Edge m) : Fin m :=
  if ω e then e.val.2 else e.val.1

theorem winner_ne_loser {m : ℕ} (ω : Orientation m) (e : Edge m) :
    winner ω e ≠ loser ω e := by
  cases h : ω e <;> simp [winner, loser, h, ne_of_lt e.property, ne_of_gt e.property]

theorem edge_winner_loser {m : ℕ} (ω : Orientation m) (e : Edge m) :
    edgeOf (winner ω e) (loser ω e) (winner_ne_loser ω e) = e := by
  apply Subtype.ext
  cases h : ω e <;>
    simp [winner, loser, h, edgeOf, min_eq_left e.property.le, max_eq_right e.property.le,
      min_eq_right e.property.le, max_eq_left e.property.le]

theorem arc_winner_loser {m : ℕ} (ω : Orientation m) (e : Edge m) :
    internalArc ω (winner ω e) (loser ω e) = true := by
  simp only [internalArc, dite_eq_right (winner_ne_loser ω e), edge_winner_loser]
  cases h : ω e <;>
    simp [winner, loser, h, e.property, not_lt_of_ge e.property.le]

theorem winner_edge {m : ℕ} (ω : Orientation m) (i j : Fin m) (hij : i ≠ j)
    (ha : internalArc ω i j = true) : winner ω (edgeOf i j hij) = i := by
  simp only [internalArc, dite_eq_right hij] at ha
  rcases lt_or_gt_of_ne hij with hl | hl
  · simp only [ite_eq_left hl] at ha
    unfold winner
    rw [ha]
    simp [edgeOf, min_eq_left hl.le]
  · simp only [ite_eq_right (not_lt_of_ge hl.le)] at ha
    have hb : ω (edgeOf i j hij) = false := by cases h : ω (edgeOf i j hij) <;> simp_all
    unfold winner
    rw [hb]
    simp [edgeOf, max_eq_left hl.le]

theorem loser_edge {m : ℕ} (ω : Orientation m) (i j : Fin m) (hij : i ≠ j)
    (ha : internalArc ω i j = true) : loser ω (edgeOf i j hij) = j := by
  simp only [internalArc, dite_eq_right hij] at ha
  rcases lt_or_gt_of_ne hij with hl | hl
  · simp only [ite_eq_left hl] at ha
    unfold loser
    rw [ha]
    simp [edgeOf, max_eq_right hl.le]
  · simp only [ite_eq_right (not_lt_of_ge hl.le)] at ha
    have hb : ω (edgeOf i j hij) = false := by cases h : ω (edgeOf i j hij) <;> simp_all
    unfold loser
    rw [hb]
    simp [edgeOf, min_eq_right hl.le]

def outDegree {m : ℕ} (T : Tournament m) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j => T.val i j = true)).card

/-- The exponent records one unit at the winner of every unordered edge. -/
def winnerExponent {m : ℕ} (ω : Orientation m) : Exponent m :=
  ∑ e : Edge m, Finsupp.single (winner ω e) 1

def outVector {m : ℕ} (T : Tournament m) : Exponent m :=
  Finsupp.equivFunOnFinite.symm (outDegree T)

/-- Edges won by i are bijective with actual out-neighbors of i. -/
def winningEdgeEquiv {m : ℕ} (ω : Orientation m) (i : Fin m) :
    {e : Edge m // winner ω e = i} ≃
      {j : Fin m // (internalTournament ω).val i j = true} where
  toFun e := ⟨loser ω e.val, by
    change internalArc ω i (loser ω e.val) = true
    simpa only [e.property] using arc_winner_loser ω e.val⟩
  invFun j :=
    let hij : i ≠ j.val := by
      intro h; have hj := j.property; rw [← h] at hj; simp [internalTournament] at hj
    ⟨edgeOf i j.val hij, winner_edge ω i j.val hij j.property⟩
  left_inv e := by
    apply Subtype.ext
    change edgeOf i (loser ω e.val) (by simpa only [e.property] using winner_ne_loser ω e.val) = e.val
    have h := edge_winner_loser ω e.val
    simpa only [e.property] using h
  right_inv j := by
    apply Subtype.ext
    apply loser_edge ω i j.val
    · intro h; have hj := j.property; rw [← h] at hj; simp [internalTournament] at hj
    · exact j.property

theorem winnerExponent_eq_outVector {m : ℕ} (ω : Orientation m) :
    winnerExponent ω = outVector (internalTournament ω) := by
  ext i
  change (∑ e : Edge m, Finsupp.single (winner ω e) 1) i = outDegree (internalTournament ω) i
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_boole]
  have h := Fintype.card_congr (winningEdgeEquiv ω i)
  simpa only [Fintype.card_subtype, outDegree, Nat.cast_id] using h

theorem outDegree_eq_sum_adjacency {m : ℕ} (T : Tournament m) (i : Fin m) :
    (outDegree T i : ℝ) = ∑ j, adjacency T i j := by
  symm
  exact Finset.sum_boole (fun j : Fin m => T.val i j = true) Finset.univ

/-- The actual manuscript signed score is determined by natural outdegree. -/
theorem score_eq_outDegree {m : ℕ} (T : Tournament m) (i : Fin m) :
    score T i = 2 * (outDegree T i : ℝ) - (m-1) := by
  rw [outDegree_eq_sum_adjacency, Finset.mul_sum]
  simp_rw [twice_adjacency]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [score]

end
end RegularOrientation
