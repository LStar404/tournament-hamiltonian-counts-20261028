module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace ForestGaussian
open scoped BigOperators
open Matrix Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual outgoing and incoming arc counts in a finite set, not assumed moment data. -/
def outCount {m : ℕ} (E : Finset (Fin m × Fin m)) (i : Fin m) : ℕ :=
  (Finset.univ.filter fun j => (i,j) ∈ E).card

def inCount {m : ℕ} (E : Finset (Fin m × Fin m)) (i : Fin m) : ℕ :=
  (Finset.univ.filter fun j => (j,i) ∈ E).card

/-- A loopless finite directed edge set with no reversed pair and at most one
incoming and one outgoing edge at each vertex. Directed cycles are permitted:
no acyclicity hypothesis is needed by the Gaussian estimate. -/
structure EdgeSet (m : ℕ) where
  edges : Finset (Fin m × Fin m)
  loopless : ∀ i, (i,i) ∉ edges
  no_reverse : ∀ i j, (i,j) ∈ edges → (j,i) ∉ edges
  out_le_one : ∀ i, outCount edges i ≤ 1
  in_le_one : ∀ i, inCount edges i ≤ 1

variable {m : ℕ} (F : EdgeSet m)

def edgeCount : ℕ := F.edges.card

def sourceCount : ℕ :=
  (Finset.univ.filter fun i => outCount F.edges i = 1 ∧ inCount F.edges i = 0).card

def imbalance (i : Fin m) : ℝ := (outCount F.edges i : ℝ) - inCount F.edges i

def graph : SimpleGraph (Fin m) where
  Adj i j := (i,j) ∈ F.edges ∨ (j,i) ∈ F.edges
  symm := ⟨by intro i j h; exact h.symm⟩
  loopless := ⟨by intro i h; exact F.loopless i (h.elim id id)⟩

instance : DecidableRel (graph F).Adj := Classical.decRel _

/-- The genuine undirected graph Laplacian attached to the actual arcs. -/
def laplacian : Matrix (Fin m) (Fin m) ℝ := (graph F).lapMatrix ℝ

lemma outCount_eq_sum (E : Finset (Fin m × Fin m)) (i : Fin m) :
    outCount E i = ∑ j : Fin m, if (i,j) ∈ E then 1 else 0 := by
  simp [outCount]

lemma inCount_eq_sum (E : Finset (Fin m × Fin m)) (i : Fin m) :
    inCount E i = ∑ j : Fin m, if (j,i) ∈ E then 1 else 0 := by
  simp [inCount]

lemma sum_outCount (E : Finset (Fin m × Fin m)) :
    ∑ i, outCount E i = E.card := by
  simp_rw [outCount_eq_sum]
  rw [← Fintype.sum_prod_type (fun p : Fin m × Fin m => if p ∈ E then (1 : ℕ) else 0)]
  simp


lemma sum_inCount (E : Finset (Fin m × Fin m)) :
    ∑ i, inCount E i = E.card := by
  simp_rw [inCount_eq_sum]
  rw [Finset.sum_comm]
  simpa only [outCount_eq_sum] using sum_outCount E

lemma edgeCount_le : edgeCount F ≤ m := by
  rw [edgeCount, ← sum_outCount]
  calc
    ∑ i, outCount F.edges i ≤ ∑ _ : Fin m, 1 := Finset.sum_le_sum (by intros; apply F.out_le_one)
    _ = m := by simp

lemma sourceCount_le : sourceCount F ≤ m := by
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

lemma sum_imbalance : ∑ i, imbalance F i = 0 := by
  simp only [imbalance, Finset.sum_sub_distrib, ← Nat.cast_sum, sum_outCount, sum_inCount,
    sub_self]

lemma imbalance_sq (i : Fin m) :
    imbalance F i ^ 2 =
      2 * (if outCount F.edges i = 1 ∧ inCount F.edges i = 0 then (1 : ℝ) else 0) -
        imbalance F i := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (F.out_le_one i) with ho | ho <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (F.in_le_one i) with hi | hi <;>
    norm_num [imbalance, ho, hi]

lemma sum_imbalance_sq : ∑ i, imbalance F i ^ 2 = 2 * (sourceCount F : ℝ) := by
  simp_rw [imbalance_sq]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_imbalance, sub_zero]
  simp [sourceCount]

lemma imbalance_abs_le (i : Fin m) : |imbalance F i| ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (F.out_le_one i) with ho | ho <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (F.in_le_one i) with hi | hi <;>
    norm_num [imbalance, ho, hi]

lemma twice_sourceCount_le : 2 * sourceCount F ≤ m := by
  have h : 2 * (sourceCount F : ℝ) ≤ m := by
    rw [← sum_imbalance_sq]
    calc
      ∑ i, imbalance F i ^ 2 ≤ ∑ _ : Fin m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact (sq_le_one_iff_abs_le_one _).mpr (imbalance_abs_le F i)
      _ = m := by simp
  exact_mod_cast h

lemma graph_degree (i : Fin m) :
    (graph F).degree i = outCount F.edges i + inCount F.edges i := by
  have hd := SimpleGraph.degree_eq_sum_if_adj (R := ℕ) (graph F) i
  simp only [Nat.cast_id] at hd
  rw [hd, outCount_eq_sum, inCount_eq_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [graph]
  by_cases h : (i,j) ∈ F.edges
  · simp [h, F.no_reverse i j h]
  · simp [h]

lemma graph_degree_le_two (i : Fin m) : (graph F).degree i ≤ 2 := by
  rw [graph_degree]
  have := F.out_le_one i
  have := F.in_le_one i
  omega

lemma sum_graph_degree : ∑ i, (graph F).degree i = 2 * edgeCount F := by
  simp_rw [graph_degree]
  rw [Finset.sum_add_distrib, sum_outCount, sum_inCount]
  simp only [edgeCount]
  omega

lemma laplacian_posSemidef : (laplacian F).PosSemidef :=
  SimpleGraph.posSemidef_lapMatrix ℝ (graph F)

lemma laplacian_isSymm : (laplacian F).IsSymm := (graph F).isSymm_lapMatrix ℝ

lemma laplacian_mulVec_one : laplacian F *ᵥ 1 = 0 :=
  (graph F).lapMatrix_mulVec_one_eq_zero ℝ

lemma laplacian_diag (i : Fin m) : laplacian F i i = (graph F).degree i := by
  simp [laplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix]

lemma laplacian_trace : Matrix.trace (laplacian F) = 2 * (edgeCount F : ℝ) := by
  simp only [Matrix.trace, Matrix.diag, laplacian_diag, ← Nat.cast_sum, sum_graph_degree,
    Nat.cast_mul, Nat.cast_ofNat]

/-- Each source has no incoming edge, so the edge/source budget is valid even
when directed cycles are allowed. -/
lemma edgeCount_add_sourceCount_le : edgeCount F + sourceCount F ≤ m := by
  have hpoint (i : Fin m) : inCount F.edges i +
      (if outCount F.edges i = 1 ∧ inCount F.edges i = 0 then 1 else 0) ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (F.in_le_one i) with hi | hi <;>
      simp [hi]
    split_ifs <;> omega
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simpa only [Finset.sum_add_distrib, sum_inCount, Finset.sum_boole,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    edgeCount, sourceCount, Nat.cast_id] using hs

lemma sourceCount_le_edgeCount : sourceCount F ≤ edgeCount F := by
  have hpoint (i : Fin m) :
      (if outCount F.edges i = 1 ∧ inCount F.edges i = 0 then 1 else 0) ≤ outCount F.edges i := by
    split_ifs with h
    · simp [h.1]
    · exact Nat.zero_le _
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simpa only [Finset.sum_boole, sum_outCount, sourceCount, edgeCount, Nat.cast_id] using hs

end
end ForestGaussian
