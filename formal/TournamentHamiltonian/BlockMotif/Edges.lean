module

public import TournamentHamiltonian.FiniteMotif.Actual
public import TournamentHamiltonian.ForestGaussian.Edges

@[expose] public section

set_option autoImplicit false
namespace BlockMotif
open TripleContraction FiniteMotif ForestGaussian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A genuine partial directed relation; cycles of length at least three are allowed. -/
structure ArcSystem (α : Type*) where
  rel : α → α → Prop
  loopless : ∀ x, ¬rel x x
  no_reverse : ∀ x y, rel x y → ¬rel y x
  out_unique : ∀ x y z, rel x y → rel x z → y=z
  in_unique : ∀ x y z, rel y x → rel z x → y=z

variable {d m : ℕ}
def encode (b : Fin d) (i : Fin m) : Fin (d*m) := finProdFinEquiv (b,i)

theorem encode_injective (b : Fin d) : Function.Injective (encode (m:=m) b) := by
  intro i j h
  exact congrArg Prod.snd (finProdFinEquiv.injective h)

def blockEdges (R : ArcSystem (Fin (d*m))) (b : Fin d) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun p => R.rel (encode b p.1) (encode b p.2))

@[simp] theorem mem_blockEdges (R : ArcSystem (Fin (d*m))) (b : Fin d) (i j : Fin m) :
    (i,j)∈blockEdges R b ↔ R.rel (encode b i) (encode b j) := by simp [blockEdges]

def blockSet (R : ArcSystem (Fin (d*m))) (b : Fin d) : EdgeSet m where
  edges := blockEdges R b
  loopless i := by simpa only [mem_blockEdges] using R.loopless (encode b i)
  no_reverse i j := by simpa only [mem_blockEdges] using R.no_reverse (encode b i) (encode b j)
  out_le_one i := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_blockEdges] at hj hk
    exact encode_injective b (R.out_unique _ _ _ hj hk)
  in_le_one i := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_blockEdges] at hj hk
    exact encode_injective b (R.in_unique _ _ _ hj hk)

def middleCount (F : EdgeSet m) : ℕ :=
  (Finset.univ.filter (fun i => outCount F.edges i=1 ∧ inCount F.edges i=1)).card

theorem edgeCount_eq_source_add_middle (F : EdgeSet m) :
    edgeCount F=sourceCount F+middleCount F := by
  have point (i : Fin m) : outCount F.edges i=
      (if outCount F.edges i=1 ∧ inCount F.edges i=0 then 1 else 0)+
      (if outCount F.edges i=1 ∧ inCount F.edges i=1 then 1 else 0) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (F.out_le_one i) with ho|ho <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (F.in_le_one i) with hi|hi <;> simp [ho,hi]
  rw [edgeCount,←sum_outCount]
  calc
    ∑ i, outCount F.edges i = ∑ i, ((if outCount F.edges i=1 ∧ inCount F.edges i=0 then 1 else 0)+(if outCount F.edges i=1 ∧ inCount F.edges i=1 then 1 else 0)) := Finset.sum_congr rfl (fun i _ => point i)
    _ = _ := by rw [Finset.sum_add_distrib]; simp [sourceCount,middleCount]

theorem edgeCount_sub_source (F : EdgeSet m) :
    edgeCount F-sourceCount F=middleCount F := by
  rw [edgeCount_eq_source_add_middle]; omega

theorem out_eq_one_iff (R : ArcSystem (Fin (d*m))) (b : Fin d) (i : Fin m) :
    outCount (blockSet R b).edges i=1 ↔ ∃j,R.rel (encode b i) (encode b j) := by
  have hle := (blockSet R b).out_le_one i
  change (Finset.univ.filter (fun j => (i,j)∈blockEdges R b)).card=1 ↔ _
  constructor
  · intro h
    have hp : (Finset.univ.filter (fun j => (i,j)∈blockEdges R b)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨j,hj⟩ := hp
    exact ⟨j,(mem_blockEdges _ _ _ _).mp (Finset.mem_filter.mp hj).2⟩
  · rintro ⟨j,hj⟩
    have hp : 0<(Finset.univ.filter (fun j => (i,j)∈blockEdges R b)).card :=
      Finset.card_pos.mpr ⟨j,by simpa using hj⟩
    change (Finset.univ.filter (fun j => (i,j)∈blockEdges R b)).card≤1 at hle
    omega

theorem in_eq_one_iff (R : ArcSystem (Fin (d*m))) (b : Fin d) (i : Fin m) :
    inCount (blockSet R b).edges i=1 ↔ ∃j,R.rel (encode b j) (encode b i) := by
  have hle := (blockSet R b).in_le_one i
  change (Finset.univ.filter (fun j => (j,i)∈blockEdges R b)).card=1 ↔ _
  constructor
  · intro h
    have hp : (Finset.univ.filter (fun j => (j,i)∈blockEdges R b)).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨j,hj⟩ := hp
    exact ⟨j,(mem_blockEdges _ _ _ _).mp (Finset.mem_filter.mp hj).2⟩
  · rintro ⟨j,hj⟩
    have hp : 0<(Finset.univ.filter (fun j => (j,i)∈blockEdges R b)).card :=
      Finset.card_pos.mpr ⟨j,by simpa using hj⟩
    change (Finset.univ.filter (fun j => (j,i)∈blockEdges R b)).card≤1 at hle
    omega

end
end BlockMotif
