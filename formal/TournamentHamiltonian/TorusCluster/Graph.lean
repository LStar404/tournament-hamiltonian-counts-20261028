module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace TorusCluster
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

variable {m : ℕ}

/-- Genuine ordered B-to-A pairs not removed by H. Disjointness is required only
when these are injected into unordered retained edges. -/
def crossPairs (H : SimpleGraph (Fin m)) (B A : Finset (Fin m)) : Finset (Fin m × Fin m) :=
  (B ×ˢ A).filter fun p => ¬ H.Adj p.1 p.2

def crossEdges (H : SimpleGraph (Fin m)) (B A : Finset (Fin m)) : Finset (Sym2 (Fin m)) :=
  (crossPairs H B A).image fun p => s(p.1,p.2)

def insideEdges (H : SimpleGraph (Fin m)) (A : Finset (Fin m)) : Finset (Sym2 (Fin m)) :=
  Hᶜ.edgeFinset.filter fun e => e.toFinset ⊆ A

lemma crossPairs_card (H : SimpleGraph (Fin m)) (B A : Finset (Fin m)) :
    (crossPairs H B A).card = ∑ i ∈ B, (A.filter fun j => ¬H.Adj i j).card := by
  simp only [crossPairs, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

lemma retained_neighbors_lower (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (A : Finset (Fin m)) (i : Fin m) :
    (A.card : ℝ)-2 ≤ (A.filter fun j => ¬H.Adj i j).card := by
  have hbad : (A.filter fun j => H.Adj i j).card ≤ H.degree i := by
    rw [← H.card_neighborFinset_eq_degree, H.neighborFinset_eq_filter]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  have hsplit : (A.filter fun j => H.Adj i j).card +
      (A.filter fun j => ¬H.Adj i j).card = A.card :=
    Finset.card_filter_add_card_filter_not (s := A) (H.Adj i)
  have hcount : A.card ≤ (A.filter fun j => ¬H.Adj i j).card+2 := by
    have := hdegree i
    omega
  have hcount' : (A.card : ℝ) ≤ (A.filter fun j => ¬H.Adj i j).card+2 := by exact_mod_cast hcount
  linarith

lemma crossPairs_lower (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (B A : Finset (Fin m)) :
    (B.card : ℝ)*((A.card : ℝ)-2) ≤ (crossPairs H B A).card := by
  rw [crossPairs_card, Nat.cast_sum]
  calc
    (B.card : ℝ)*((A.card : ℝ)-2) = ∑ _i ∈ B, ((A.card : ℝ)-2) := by simp; ring
    _ ≤ ∑ i ∈ B, ((A.filter fun j => ¬H.Adj i j).card : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact retained_neighbors_lower H hdegree A i

lemma crossEdges_card (H : SimpleGraph (Fin m)) (B A : Finset (Fin m))
    (hdisj : Disjoint B A) : (crossEdges H B A).card = (crossPairs H B A).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  have hp' := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1)
  have hq' := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1)
  rcases Sym2.mk_eq_mk_iff.mp he with he | he
  · exact he
  · exfalso
    have he' : p.1 = q.2 := congrArg Prod.fst he
    exact Finset.disjoint_left.mp hdisj hp'.1 (he' ▸ hq'.2)

lemma crossEdges_lower (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (B A : Finset (Fin m)) (hdisj : Disjoint B A) :
    (B.card : ℝ)*((A.card : ℝ)-2) ≤ (crossEdges H B A).card := by
  rw [crossEdges_card H B A hdisj]
  exact crossPairs_lower H hdegree B A

lemma crossEdges_subset (H : SimpleGraph (Fin m)) (B A : Finset (Fin m))
    (hdisj : Disjoint B A) : crossEdges H B A ⊆ Hᶜ.edgeFinset := by
  intro e he
  obtain ⟨⟨i,j⟩, hp, rfl⟩ := Finset.mem_image.mp he
  have h := Finset.mem_filter.mp hp
  have hp' := Finset.mem_product.mp h.1
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
  refine ⟨?_, h.2⟩
  intro heq
  subst j
  exact Finset.disjoint_left.mp hdisj hp'.1 hp'.2

lemma insideEdges_subset (H : SimpleGraph (Fin m)) (A : Finset (Fin m)) :
    insideEdges H A ⊆ Hᶜ.edgeFinset := Finset.filter_subset _ _

lemma cross_inside_disjoint (H : SimpleGraph (Fin m)) (B I A : Finset (Fin m))
    (hBA : Disjoint B A) : Disjoint (crossEdges H B I) (insideEdges H A) := by
  apply Finset.disjoint_left.mpr
  intro e he hi
  obtain ⟨⟨i,j⟩, hp, rfl⟩ := Finset.mem_image.mp he
  have hb := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have ha := (Finset.mem_filter.mp hi).2
  have hia : i ∈ A := ha (by simp)
  exact Finset.disjoint_left.mp hBA hb hia

/-- The m²/128 constant follows from actual missing-degree counts. -/
theorem far_cross_count (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (hm : 64 ≤ m) (B C : Finset (Fin m)) (hdisj : Disjoint B C)
    (hB : (m : ℝ)/4 ≤ B.card) (hC : (m : ℝ)/16 ≤ C.card) :
    (m : ℝ)^2/128 ≤ (crossEdges H B C).card := by
  have hm' : (64 : ℝ) ≤ m := by exact_mod_cast hm
  have hCn : 0 ≤ (C.card : ℝ)-2 := by linarith
  have hl := crossEdges_lower H hdegree B C hdisj
  have h1 := mul_le_mul_of_nonneg_right hB hCn
  have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_right hC 2) (by positivity : 0 ≤ (m : ℝ)/4)
  have hh : (m : ℝ)^2/128 ≤ (m:ℝ)/4*((m:ℝ)/16-2) := by nlinarith
  exact hh.trans (h2.trans (h1.trans hl))

/-- Outlier loss is paid while retaining all inside-edge factors. -/
theorem outlier_cross_count (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (hm : 64 ≤ m) (B I : Finset (Fin m)) (hdisj : Disjoint B I)
    (hI : 3*(m : ℝ)/4 < I.card) :
    (m : ℝ)*B.card/2 ≤ (crossEdges H B I).card := by
  have hm' : (64 : ℝ) ≤ m := by exact_mod_cast hm
  have hl := crossEdges_lower H hdegree B I hdisj
  have hp : (m : ℝ)/2 ≤ (I.card : ℝ)-2 := by linarith
  have := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ B.card)
  nlinarith

end
end TorusCluster
