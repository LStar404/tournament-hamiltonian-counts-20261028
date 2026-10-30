module

public import TournamentHamiltonian.ForestGaussian.Factor

@[expose] public section

set_option autoImplicit false

namespace ForestGaussian
open scoped BigOperators
open Matrix
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ}

/-- The empty actual edge set exists also for m=0 and m=1. -/
def emptyEdgeSet (m : ℕ) : EdgeSet m where
  edges := ∅
  loopless := by simp
  no_reverse := by simp
  out_le_one := by simp [outCount]
  in_le_one := by simp [inCount]

lemma emptyEdgeSet_graph : graph (emptyEdgeSet m) = ⊥ := by
  ext i j
  simp [graph, emptyEdgeSet]

lemma emptyEdgeSet_laplacian : laplacian (emptyEdgeSet m) = 0 := by
  have hd (i : Fin m) : (graph (emptyEdgeSet m)).degree i = 0 := by
    rw [graph_degree]
    simp [emptyEdgeSet, outCount, inCount]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [laplacian_diag, hd]
  · simp [laplacian, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix, graph, emptyEdgeSet, hij]

lemma emptyEdgeSet_imbalance : imbalance (emptyEdgeSet m) = 0 := by
  ext i
  simp [imbalance, emptyEdgeSet, outCount, inCount]

lemma gaussianFactor_empty : gaussianFactor (emptyEdgeSet m) = 1 := by
  simp [gaussianFactor, emptyEdgeSet_laplacian, emptyEdgeSet_imbalance, factor, complement]

lemma gaussianComplement_mulVec_one (F : EdgeSet m) :
    complement (laplacian F) (m : ℝ) *ᵥ (1 : Fin m → ℝ) = 1 :=
  complement_mulVec_one (m : ℝ) (laplacian_mulVec_one F)

lemma gaussianComplement_inv_mulVec_one (F : EdgeSet m) (hm : 8 ≤ m) :
    (complement (laplacian F) (m : ℝ))⁻¹ *ᵥ (1 : Fin m → ℝ) = 1 :=
  by
    have h := complement_inv_mulVec_one (ι := Fin m) (L := laplacian F) (m := (m : ℝ))
      (gaussianComplement_posDef F hm) (laplacian_mulVec_one F)
    have hdec : Classical.decEq (Fin m) = instDecidableEqFin m := Subsingleton.elim _ _
    rw [hdec] at h
    exact h

lemma imbalance_phase_translation_invariant (F : EdgeSet m) (x : Fin m → ℝ) (t : ℝ) :
    imbalance F ⬝ᵥ (x + t • (1 : Fin m → ℝ)) = imbalance F ⬝ᵥ x :=
  phase_translation_invariant (imbalance F) x t (sum_imbalance F)

end
end ForestGaussian
