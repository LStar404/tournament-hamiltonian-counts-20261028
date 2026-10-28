module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Finite Hamilton paths and random vertex augmentation

This file verifies the finite combinatorial identity used in Lemma 11.5,
§11.6 of `manuscripts/01_combined.zh.md` (2026-10-28), not the analytic
or asymptotic estimates elsewhere in the paper.

A Hamilton path is an actual permutation whose consecutive edges point
forwards. A Hamilton cycle on `Option V` is represented canonically by
starting at the distinguished vertex `none`, followed by a permutation of
all the old vertices. Thus cycles are counted once, not once per cyclic
starting point. The finite sample space `V → Bool` independently orients
all the new edges. The counting identity implies that the uniform average
cycle count is exactly one quarter of the path count.

The main identity requires at least two old vertices: the first and last
vertices must be distinct. The one-old-vertex case is explicitly refuted
below. No assertion of the determinant–permanent convolution is made.
-/

public section

namespace TournamentPaths

/-- A loopless orientation of the complete graph, with Boolean adjacency. -/
structure Tournament (V : Type*) where
  edge : V → V → Bool
  loopless : ∀ v, edge v v = false
  oriented : ∀ u v, u ≠ v → edge u v = !(edge v u)

/-- Add one distinguished vertex. `f v = true` means the new vertex points to `v`. -/
def augment {V : Type*} (T : Tournament V) (f : V → Bool) :
    Tournament (Option V) where
  edge
    | none, none => false
    | none, some v => f v
    | some v, none => !(f v)
    | some u, some v => T.edge u v
  loopless := by
    intro v
    cases v with
    | none => rfl
    | some v => exact T.loopless v
  oriented := by
    intro u v h
    cases u <;> cases v
    · exact False.elim (h rfl)
    · simp
    · rfl
    · apply T.oriented
      intro he
      exact h (congrArg some he)

/-- The consecutive-edge condition for an ordering of all `n+1` vertices. -/
def IsHamiltonPath {n : ℕ} (T : Tournament (Fin (n + 1)))
    (p : Equiv.Perm (Fin (n + 1))) : Prop :=
  ∀ i : Fin n, T.edge (p i.castSucc) (p i.succ) = true

/-- Canonical Hamilton cycles, starting at the unique distinguished vertex.
The permutation lists every other vertex exactly once. -/
def IsRootedHamiltonCycle {n : ℕ} (T : Tournament (Option (Fin (n + 1))))
    (p : Equiv.Perm (Fin (n + 1))) : Prop :=
  T.edge none (some (p 0)) = true ∧
  (∀ i : Fin n, T.edge (some (p i.castSucc)) (some (p i.succ)) = true) ∧
  T.edge (some (p (Fin.last n))) none = true

/-- Number of Hamilton paths, counted by their vertex order. -/
noncomputable def pathCount {n : ℕ} (T : Tournament (Fin (n + 1))) : ℕ := by
  classical
  exact ∑ p : Equiv.Perm (Fin (n + 1)), if IsHamiltonPath T p then 1 else 0

/-- Number of Hamilton cycles, counted once by their order after `none`. -/
noncomputable def rootedCycleCount {n : ℕ}
    (T : Tournament (Option (Fin (n + 1)))) : ℕ := by
  classical
  exact ∑ p : Equiv.Perm (Fin (n + 1)), if IsRootedHamiltonCycle T p then 1 else 0

/-- Deleting the new vertex leaves precisely a Hamilton path, with the two
required new edge orientations. This is the exact path/cycle correspondence. -/
theorem augmented_cycle_iff {n : ℕ} (T : Tournament (Fin (n + 1)))
    (f : Fin (n + 1) → Bool) (p : Equiv.Perm (Fin (n + 1))) :
    IsRootedHamiltonCycle (augment T f) p ↔
      IsHamiltonPath T p ∧ f (p 0) = true ∧ f (p (Fin.last n)) = false := by
  simp only [IsRootedHamiltonCycle, augment, IsHamiltonPath, Bool.not_eq_true_eq_eq_false]
  tauto

/-- Two distinct coordinates of a Boolean function take prescribed opposite
values on exactly one quarter of the finite function space. This is a counting
statement, not an assumption of probabilistic independence. -/
theorem four_mul_two_coordinate_count {V : Type*} [Fintype V] [DecidableEq V]
    (a b : V) (hab : a ≠ b) :
    4 * (∑ f : V → Bool, if f a = true ∧ f b = false then (1 : ℕ) else 0) =
      Fintype.card (V → Bool) := by
  classical
  let B := {v : V // v ≠ a}
  let b' : B := ⟨b, Ne.symm hab⟩
  let K := {v : B // v ≠ b'}
  let e : (V → Bool) ≃ Bool × (Bool × (K → Bool)) :=
    (Equiv.funSplitAt a Bool).trans
      (Equiv.prodCongr (Equiv.refl Bool) (Equiv.funSplitAt b' Bool))
  have hs : (∑ f : V → Bool,
      if f a = true ∧ f b = false then (1 : ℕ) else 0) = Fintype.card (K → Bool) := by
    calc
      _ = ∑ g : Bool × (Bool × (K → Bool)),
          if g.1 = true ∧ g.2.1 = false then (1 : ℕ) else 0 := by
        apply Fintype.sum_equiv e
        intro f
        rfl
      _ = _ := by
        simp only [Fintype.sum_prod_type, Fintype.sum_bool]
        simp
  have hc : Fintype.card (V → Bool) = 4 * Fintype.card (K → Bool) := by
    calc
      _ = Fintype.card (Bool × (Bool × (K → Bool))) := Fintype.card_congr e
      _ = _ := by simp [Fintype.card_prod]; omega
  rw [hs, hc]

/-- Exact integral counting form of Lemma 11.5. With `n+2` old vertices,
four times the sum of augmented cycle counts equals the sample-space size
times the original path count. -/
theorem augmentation_count_identity {n : ℕ} (T : Tournament (Fin (n + 2))) :
    4 * (∑ f : Fin (n + 2) → Bool, rootedCycleCount (augment T f)) =
      2 ^ (n + 2) * pathCount T := by
  classical
  unfold rootedCycleCount pathCount
  rw [Finset.sum_comm, Finset.mul_sum]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpath : IsHamiltonPath T p
  · have hend : p 0 ≠ p (Fin.last (n + 1)) := by
      intro he
      have hz := p.injective he
      have hv := congrArg Fin.val hz
      simp only [Fin.val_zero, Fin.val_last] at hv
      omega
    simp only [hpath, ↓reduceIte, mul_one]
    simp_rw [augmented_cycle_iff, hpath, true_and]
    simpa using four_mul_two_coordinate_count (p 0) (p (Fin.last (n + 1))) hend
  · simp [augmented_cycle_iff, hpath]

/-- Uniform expectation over all independent orientations of the new edges.
This is a rational finite average; no measure-theoretic independence hypotheses
or conditional-expectation assumptions are hidden in the statement. -/
noncomputable def uniformAugmentedCycleAverage {n : ℕ}
    (T : Tournament (Fin (n + 1))) : ℚ :=
  ((∑ f : Fin (n + 1) → Bool, rootedCycleCount (augment T f) : ℕ) : ℚ) /
    (2 : ℚ) ^ (n + 1)

/-- The conditional expectation conclusion of Lemma 11.5, for a fixed tournament
with at least two old vertices. -/
theorem augmentation_average {n : ℕ} (T : Tournament (Fin (n + 2))) :
    uniformAugmentedCycleAverage T = (pathCount T : ℚ) / 4 := by
  unfold uniformAugmentedCycleAverage
  have h : (4 : ℚ) *
      ((∑ f : Fin (n + 2) → Bool, rootedCycleCount (augment T f) : ℕ) : ℚ) =
      (2 : ℚ) ^ (n + 2) * (pathCount T : ℚ) := by
    exact_mod_cast augmentation_count_identity T
  apply (div_eq_div_iff (pow_ne_zero _ (by norm_num)) (by norm_num)).2
  nlinarith

/-- On one old vertex there is one Hamilton path, including its empty edge set. -/
theorem one_vertex_path_count (T : Tournament (Fin 1)) : pathCount T = 1 := by
  simp [pathCount, IsHamiltonPath]

/-- On one old vertex the two required new edges are opposite orientations of
the same undirected edge; no augmented directed Hamilton cycle exists. -/
theorem one_vertex_augmented_cycle_count (T : Tournament (Fin 1))
    (f : Fin 1 → Bool) : rootedCycleCount (augment T f) = 0 := by
  classical
  unfold rootedCycleCount
  apply Finset.sum_eq_zero
  intro p hp
  have hnot : ¬ IsRootedHamiltonCycle (augment T f) p := by
    rw [augmented_cycle_iff]
    intro h
    have he : f (p 0) = false := h.2.2
    rw [h.2.1] at he
    contradiction
  simp [hnot]

/-- Explicit boundary check: the one-vertex analogue of `H/4` is false. -/
theorem one_vertex_average_not_quarter (T : Tournament (Fin 1)) :
    uniformAugmentedCycleAverage T ≠ (pathCount T : ℚ) / 4 := by
  simp [uniformAugmentedCycleAverage, one_vertex_augmented_cycle_count,
    one_vertex_path_count]

end TournamentPaths
