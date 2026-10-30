module

public import TournamentHamiltonian.BlockMotif.Regular

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BlockMotif
open TripleContraction FiniteMotif ForestGaussian TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ}

def arcs (R : ArcSystem (Fin (d*m))) : Finset (Fin (d*m) × Fin (d*m)) :=
  Finset.univ.filter (fun p => R.rel p.1 p.2)

def internalArcs (R : ArcSystem (Fin (d*m))) : Finset (Fin (d*m) × Fin (d*m)) :=
  (arcs R).filter (fun p => block p.1=block p.2)

def arcProduct (R : ArcSystem (Fin (d*m))) (A : Matrix (Fin (d*m)) (Fin (d*m)) ℝ) : ℝ :=
  ∏p∈arcs R,A p.1 p.2

/-- Reindexing both endpoints, the internal arcs are partitioned by their actual block. -/
theorem internal_card (R : ArcSystem (Fin (d*m))) :
    (internalArcs R).card=∑b,edgeCount (blockSet R b) := by
  simp only [internalArcs,arcs,Finset.filter_filter,Finset.card_filter]
  have he := Fintype.sum_equiv (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)
    (fun p : (Fin d×Fin m)×(Fin d×Fin m) =>
      if R.rel (finProdFinEquiv p.1) (finProdFinEquiv p.2) ∧ p.1.1=p.2.1 then (1:ℕ) else 0)
    (fun p : Fin (d*m)×Fin (d*m) => if R.rel p.1 p.2 ∧ block p.1=block p.2 then (1:ℕ) else 0)
    (by intro p; simp [block])
  rw [←he]
  simp only [Fintype.sum_prod_type]
  simp_rw [and_comm,ite_and,Finset.sum_ite_irrel]
  simp only [edgeCount,blockSet,blockEdges,Finset.card_filter,Fintype.sum_prod_type,encode]
  simp only [Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]


theorem weightFin_arc (R : ArcSystem (Fin (d*m))) (T : Tournament d)
    (u v : Fin (d*m)) (huv : R.rel u v) :
    UniformDeletion.weightFin T u v=
      if block u=block v then (1/2:ℝ) else if T.val (block u) (block v)=true then 1 else 0 := by
  have hne : u≠v := by intro h; subst v; exact R.loopless u huv
  change UniformBlowup.weight T (finProdFinEquiv.symm u) (finProdFinEquiv.symm v)=_
  rw [UniformBlowup.weight,ite_eq_right (finProdFinEquiv.symm.injective.ne hne)]
  rfl

/-- The uniform candidate monomial, with an explicit zero branch for every
cross-incompatible candidate. There is no division by its possibly zero weight. -/
theorem arcProduct_uniform (R : ArcSystem (Fin (d*m))) (T : Tournament d) :
    arcProduct R (UniformDeletion.weightFin T)=
      (if CrossCompatible R T then (1:ℝ) else 0)*(1/2:ℝ)^(∑b,edgeCount (blockSet R b)) := by
  by_cases hc : CrossCompatible R T
  · simp only [hc,ite_true,one_mul]
    rw [←internal_card]
    have he : arcProduct R (UniformDeletion.weightFin T)=
        ∏p∈arcs R,if block p.1=block p.2 then (1/2:ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro p hp
      have hr : R.rel p.1 p.2 := (Finset.mem_filter.mp hp).2
      rw [weightFin_arc R T _ _ hr]
      by_cases hb : block p.1=block p.2
      · simp only [hb,ite_true]
      · simp only [hb,ite_false,hc _ _ hr hb,ite_true]
    rw [he,Finset.prod_ite]
    simp only [Finset.prod_const,one_pow,mul_one,internalArcs]
  · simp only [hc,ite_false,zero_mul]
    have hfail : ∃u v,R.rel u v ∧ block u≠block v ∧ T.val (block u) (block v)≠true := by
      by_contra hf
      apply hc
      intro u v hr hb
      by_contra ht
      exact hf ⟨u,v,hr,hb,ht⟩
    obtain ⟨u,v,hr,hb,ht⟩ := hfail
    apply Finset.prod_eq_zero (show (u,v)∈arcs R by simp [arcs,hr])
    rw [weightFin_arc R T _ _ hr,ite_eq_right hb,ite_eq_right ht]

/-- The exact successor monomial is a product over the actual directed relation. -/
theorem cycle_monomial_arcs (hN : 3≤d*m) (σ : Full (Fin (d*m)))
    (A : Matrix (Fin (d*m)) (Fin (d*m)) ℝ) :
    monomial A σ.val=arcProduct (cycleSystem hN σ) A := by
  apply Finset.prod_bij (fun u _ => (u,σ.val u))
  · intro u _; simp [arcs,cycleSystem]
  · intro u _ v _ h; exact congrArg Prod.fst h
  · intro p hp
    have hp : σ.val p.1=p.2 := (Finset.mem_filter.mp hp).2
    exact ⟨p.1,Finset.mem_univ _,Prod.ext rfl hp⟩
  · intro u _; rfl

/-- Every non-wrapping ordering edge appears exactly once, including the empty product. -/
theorem path_monomial_arcs (π : Ordering (Fin (d*m)))
    (A : Matrix (Fin (d*m)) (Fin (d*m)) ℝ) :
    pathMonomial A π=arcProduct (pathSystem π) A := by
  apply Finset.prod_bij (fun r _ => (π r.val.1,π r.val.2))
  · intro r _; simp only [arcs,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨r,rfl,rfl⟩
  · intro r _ s _ h
    apply Subtype.ext
    exact Prod.ext (π.injective (congrArg Prod.fst h)) (π.injective (congrArg Prod.snd h))
  · intro p hp
    obtain ⟨r,hu,hv⟩ := (Finset.mem_filter.mp hp).2
    exact ⟨r,Finset.mem_univ _,Prod.ext hu hv⟩
  · intro r _; rfl

end
end BlockMotif
