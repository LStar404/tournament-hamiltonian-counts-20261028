module

public import TournamentHamiltonian.BlockMotif.Edges

@[expose] public section

set_option autoImplicit false
namespace BlockMotif
open TripleContraction FiniteMotif ForestGaussian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ}

def Present (R : ArcSystem (Fin (d*m))) (t : Motif d m) : Prop :=
  R.rel (t.vertex 0) (t.vertex 1) ∧ R.rel (t.vertex 1) (t.vertex 2)

def present (R : ArcSystem (Fin (d*m))) : Finset (Motif d m) := Finset.univ.filter (Present R)

def middleVertices (R : ArcSystem (Fin (d*m))) : Finset (Fin d × Fin m) :=
  Finset.univ.filter (fun p => outCount (blockSet R p.1).edges p.2=1 ∧
    inCount (blockSet R p.1).edges p.2=1)

theorem middle_mem (R : ArcSystem (Fin (d*m))) (t : Motif d m) (ht : t∈present R) :
    (t.1,t.2 1)∈middleVertices R := by
  have ht : Present R t := (Finset.mem_filter.mp ht).2
  simp only [middleVertices,Finset.mem_filter,Finset.mem_univ,true_and,out_eq_one_iff,in_eq_one_iff]
  exact ⟨⟨t.2 2,ht.2⟩,⟨t.2 0,ht.1⟩⟩

theorem middle_injective (R : ArcSystem (Fin (d*m))) (t s : Motif d m)
    (ht : t∈present R) (hs : s∈present R) (he : (t.1,t.2 1)=(s.1,s.2 1)) : t=s := by
  have ht : Present R t := (Finset.mem_filter.mp ht).2
  have hs : Present R s := (Finset.mem_filter.mp hs).2
  have hm : t.vertex 1=s.vertex 1 := congrArg finProdFinEquiv he
  apply Motif.ext_vertex
  intro i
  fin_cases i
  · exact R.in_unique _ _ _ ht.1 (hm ▸ hs.1)
  · exact hm
  · exact R.out_unique _ _ _ ht.2 (hm ▸ hs.2)

theorem middle_surjective (R : ArcSystem (Fin (d*m))) (p : Fin d × Fin m)
    (hp : p∈middleVertices R) : ∃t∈present R,(t.1,t.2 1)=p := by
  have hp : outCount (blockSet R p.1).edges p.2=1 ∧ inCount (blockSet R p.1).edges p.2=1 :=
    (Finset.mem_filter.mp hp).2
  obtain ⟨v,hv⟩ := (out_eq_one_iff R p.1 p.2).mp hp.1
  obtain ⟨u,hu⟩ := (in_eq_one_iff R p.1 p.2).mp hp.2
  have hui : u≠p.2 := by intro h; subst u; exact R.loopless _ hu
  have hiv : p.2≠v := by intro h; subst v; exact R.loopless _ hv
  have huv : u≠v := by intro h; subst v; exact R.no_reverse _ _ hu hv
  let e : Fin 3 ↪ Fin m := ⟨![u,p.2,v],by
    intro i j h
    fin_cases i <;> fin_cases j <;> dsimp at h <;> simp_all⟩
  refine ⟨(p.1,e),?_,by change (p.1,p.2)=p; rfl⟩
  simp only [present,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨hu,hv⟩

/-- A genuine bijective count: each two-edge internal occurrence has exactly one
middle vertex, and every internal in/out middle vertex supplies its distinct triple. -/
theorem present_card_eq_middle (R : ArcSystem (Fin (d*m))) :
    (present R).card=(middleVertices R).card := by
  apply Finset.card_bij (fun t _ => (t.1,t.2 1))
  · exact middle_mem R
  · intro t ht s hs he
    exact middle_injective R t s ht hs he
  · intro p hp
    obtain ⟨t,ht,he⟩ := middle_surjective R p hp
    exact ⟨t,ht,he⟩

theorem middle_card_eq_sum (R : ArcSystem (Fin (d*m))) :
    (middleVertices R).card=∑b,middleCount (blockSet R b) := by
  simp only [middleVertices,Finset.card_filter,middleCount]
  rw [Fintype.sum_prod_type]

/-- The a-s identity holds without any acyclicity restriction. -/
theorem sum_edge_sub_source (R : ArcSystem (Fin (d*m))) :
    (∑b,(edgeCount (blockSet R b)-sourceCount (blockSet R b)))=(present R).card := by
  simp_rw [edgeCount_sub_source]
  rw [present_card_eq_middle,middle_card_eq_sum]

end
end BlockMotif
