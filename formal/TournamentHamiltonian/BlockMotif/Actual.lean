module

public import TournamentHamiltonian.BlockMotif.Count

@[expose] public section

set_option autoImplicit false
namespace BlockMotif
open TripleContraction FiniteMotif ForestGaussian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ}

theorem full_not_two {α : Type*} [Fintype α] [DecidableEq α]
    (hN : 3≤Fintype.card α) (σ : Full α) (u : α) : σ.val (σ.val u)≠u := by
  have h2 : 2≤Fintype.card α := by omega
  have hs := (WeightedCycle.singleFullCycle_iff_cycle_support h2 σ.val).mp σ.property
  have hn := cycle_successor_ne h2 σ.val σ.property u
  intro h
  have he := hs.1.eq_swap_of_apply_apply_eq_self hn h
  have hc : σ.val.support.card=2 := by
    rw [he]
    exact Equiv.Perm.card_support_swap hn.symm
  rw [hs.2,Finset.card_univ] at hc
  omega

def cycleSystem (hN : 3≤d*m) (σ : Full (Fin (d*m))) : ArcSystem (Fin (d*m)) where
  rel u v := σ.val u=v
  loopless u := cycle_successor_ne (by simpa using (show 2≤d*m by omega)) σ.val σ.property u
  no_reverse u v huv hvu := full_not_two (by simpa using hN) σ u (by rw [huv,hvu])
  out_unique _ _ _ h1 h2 := h1.symm.trans h2
  in_unique _ _ _ h1 h2 := σ.val.injective (h1.trans h2.symm)

theorem pathArc_iff_positions {α : Type*} [Fintype α] [DecidableEq α]
    (π : Ordering α) (u v : α) :
    PathArc π u v ↔ (π.symm v).val=(π.symm u).val+1 := by
  constructor
  · rintro ⟨r,hu,hv⟩
    rw [←hu,←hv]
    simpa using r.property
  · intro h
    exact ⟨⟨(π.symm u,π.symm v),h⟩,π.apply_symm_apply u,π.apply_symm_apply v⟩

def pathSystem (π : Ordering (Fin (d*m))) : ArcSystem (Fin (d*m)) where
  rel := PathArc π
  loopless u := by rw [pathArc_iff_positions]; omega
  no_reverse u v := by simp only [pathArc_iff_positions]; omega
  out_unique u v w hv hw := by
    rw [pathArc_iff_positions] at hv hw
    apply π.symm.injective
    apply Fin.ext
    omega
  in_unique u v w hv hw := by
    rw [pathArc_iff_positions] at hv hw
    apply π.symm.injective
    apply Fin.ext
    omega

@[simp] theorem cycle_present (hN : 3≤d*m) (σ : Full (Fin (d*m))) (t : Motif d m) :
    Present (cycleSystem hN σ) t ↔ CycleOccurs σ t := Iff.rfl

@[simp] theorem path_present (π : Ordering (Fin (d*m))) (t : Motif d m) :
    Present (pathSystem π) t ↔ PathOccurs π t := Iff.rfl

theorem cycle_a_sub_s (hN : 3≤d*m) (σ : Full (Fin (d*m))) :
    (∑b,(edgeCount (blockSet (cycleSystem hN σ) b)-sourceCount (blockSet (cycleSystem hN σ) b)))=cycleA σ := by
  rw [sum_edge_sub_source,cycleA_eq_card]
  simp only [present,cycle_present]

theorem path_a_sub_s (π : Ordering (Fin (d*m))) :
    (∑b,(edgeCount (blockSet (pathSystem π) b)-sourceCount (blockSet (pathSystem π) b)))=pathA π := by
  rw [sum_edge_sub_source,pathA_eq_card]
  simp only [present,path_present]

end
end BlockMotif
