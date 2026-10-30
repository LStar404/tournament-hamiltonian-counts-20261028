module

public import TournamentHamiltonian.FiniteMotif.Basic

@[expose] public section

set_option autoImplicit false
namespace FiniteMotif
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev DisjointPair (d m : ℕ) := {p : Motif d m × Motif d m // p.1.Disjoint p.2}
abbrev LocalDisjoint (m : ℕ) :=
  {p : (Fin 3 ↪ Fin m) × (Fin 3 ↪ Fin m) // Disjoint (Set.range p.1) (Set.range p.2)}
abbrev DifferentPair (d m : ℕ) :=
  {b : Fin d × Fin d // b.1≠b.2} × ((Fin 3 ↪ Fin m) × (Fin 3 ↪ Fin m))

/-- Splitting six labels into the first and second directed triples. -/
def sixEquiv (m : ℕ) : (Fin 6 ↪ Fin m) ≃ LocalDisjoint m :=
  (Equiv.embeddingCongr (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm
    (Equiv.refl _)).trans Equiv.sumEmbeddingEquivProdEmbeddingDisjoint

/-- Both ordered block cases; the equal-block summand is not omitted. -/
def disjointPairEquiv (d m : ℕ) :
    DisjointPair d m ≃ DifferentPair d m ⊕ (Fin d × LocalDisjoint m) where
  toFun p := if h : p.val.1.1=p.val.2.1 then
      Sum.inr (p.val.1.1,⟨(p.val.1.2,p.val.2.2),by
        rcases (Motif.disjoint_iff _ _).mp p.property with hn|hd
        · exact (hn h).elim
        · exact hd⟩)
    else Sum.inl (⟨(p.val.1.1,p.val.2.1),h⟩,(p.val.1.2,p.val.2.2))
  invFun p := match p with
    | Sum.inl q => ⟨((q.1.val.1,q.2.1),(q.1.val.2,q.2.2)),
        (Motif.disjoint_iff _ _).mpr (Or.inl q.1.property)⟩
    | Sum.inr q => ⟨((q.1,q.2.val.1),(q.1,q.2.val.2)),
        (Motif.disjoint_iff _ _).mpr (Or.inr q.2.property)⟩
  left_inv p := by
    rcases p with ⟨⟨⟨b,f⟩,⟨c,g⟩⟩,hp⟩
    by_cases h : b=c
    · subst c; simp
    · simp [h]
  right_inv p := by
    rcases p with q|q
    · rcases q with ⟨⟨⟨b,c⟩,h⟩,f,g⟩; simp [h]
    · rcases q with ⟨b,⟨⟨f,g⟩,h⟩⟩; simp

/-- The second summand is literally one six-label embedding in one block. -/
def disjointPairEmbSixEquiv (d m : ℕ) :
    DisjointPair d m ≃ DifferentPair d m ⊕ (Fin d × (Fin 6 ↪ Fin m)) :=
  (disjointPairEquiv d m).trans (Equiv.sumCongr (Equiv.refl _)
    (Equiv.prodCongr (Equiv.refl _) (sixEquiv m).symm))

def twoEmbeddingEquiv (d : ℕ) :
    (Fin 2 ↪ Fin d) ≃ {b : Fin d × Fin d // b.1≠b.2} where
  toFun f := ⟨(f 0,f 1),f.injective.ne (by decide)⟩
  invFun b := ⟨![b.val.1,b.val.2],by
    intro i j h
    have hb := b.property
    fin_cases i <;> fin_cases j <;> simp_all⟩
  left_inv f := by apply DFunLike.ext; intro i; fin_cases i <;> rfl
  right_inv b := by rcases b with ⟨⟨a,b⟩,h⟩; rfl

theorem card_different_pair (d m : ℕ) :
    Fintype.card (DifferentPair d m)=d*(d-1)*(m.descFactorial 3)^2 := by
  simp only [DifferentPair,Fintype.card_prod]
  rw [← Fintype.card_congr (twoEmbeddingEquiv d)]
  simp only [Fintype.card_embedding_eq,Fintype.card_fin]
  simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero]
  ring

/-- Ordered disjoint pairs, including both motifs inside the same block. -/
theorem card_disjoint_pair (d m : ℕ) :
    Fintype.card (DisjointPair d m)=
      d*(d-1)*(m.descFactorial 3)^2+d*m.descFactorial 6 := by
  rw [Fintype.card_congr (disjointPairEmbSixEquiv d m),Fintype.card_sum,
    card_different_pair]
  simp

theorem card_motif_expanded (d m : ℕ) :
    Fintype.card (Motif d m)=d*m*(m-1)*(m-2) := by
  rw [card_motif]
  simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero]
  ring

end
end FiniteMotif
