module

public import TournamentHamiltonian.TripleContraction.Splice
public import TournamentHamiltonian.UniformFinal.UniformNormalization

@[expose] public section

set_option autoImplicit false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual forward successor monomial. -/
def monomial (A : Matrix α α ℝ) (σ : Equiv.Perm α) : ℝ := ∏ x, A x (σ x)

def eraseMatrix (A : Matrix α α ℝ) (v : α) : Matrix (Retain v) (Retain v) ℝ :=
  A.submatrix Subtype.val Subtype.val

/-- Only off-diagonal outgoing entries must agree. -/
def RowTwins (A : Matrix α α ℝ) (u v : α) : Prop :=
  ∀ x, x ≠ u → x ≠ v → A v x = A u x

/-- Splitting one actual ambient product into its deleted factor and retained factors. -/
theorem prod_split (f : α → ℝ) (v : α) : (∏ x, f x) = f v * ∏ x : Retain v, f x.val := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun x => x = v) f]
  congr 1
  let : Fintype {x : α // x=v} := Subtype.fintype (fun x => x=v)
  exact Fintype.prod_subsingleton (fun x : {x : α // x=v} => f x.val) ⟨v,rfl⟩

/-- Insertion changes exactly the prescribed edge factor. No division and no
nonzero or positivity hypothesis on the entries occurs. -/
theorem splice_monomial (A : Matrix α α ℝ) {u v : α} (huv : u ≠ v)
    (hrow : RowTwins A u v) (τ : Equiv.Perm (Retain v))
    (hne : τ ⟨u,huv⟩ ≠ ⟨u,huv⟩) :
    monomial A (splice u v τ) = A u v * monomial (eraseMatrix A v) τ := by
  have htu : (τ ⟨u,huv⟩).val ≠ u := by
    intro h
    exact hne (Subtype.ext h)
  have htw := hrow (τ ⟨u,huv⟩).val htu (τ ⟨u,huv⟩).property
  unfold monomial
  rw [prod_split _ v, splice_at_new huv]
  rw [prod_split (fun x : Retain v => A x.val (splice u v τ x.val)) ⟨u,huv⟩]
  rw [prod_split (fun x : Retain v => eraseMatrix A v x (τ x)) ⟨u,huv⟩]
  simp only [splice_at_left, eraseMatrix, Matrix.submatrix_apply]
  rw [htw]
  have hp : (∏ x : Retain (⟨u,huv⟩ : Retain v), A x.val.val (splice u v τ x.val.val)) =
      ∏ x : Retain (⟨u,huv⟩ : Retain v), A x.val.val (τ x.val).val := by
    apply Finset.prod_congr rfl
    intro x _
    rw [splice_at_other (fun h => x.property (Subtype.ext h)) x.val.property]
  rw [hp]
  ring

theorem cycle_successor_ne {β : Type*} [Fintype β] [DecidableEq β]
    (hβ : 2 ≤ Fintype.card β) (τ : Equiv.Perm β) (hτ : SingleFullCycle τ) (x : β) :
    τ x ≠ x := by
  have hs := ((singleFullCycle_iff_cycle_support hβ τ).mp hτ).2
  exact Equiv.Perm.mem_support.mp (hs ▸ Finset.mem_univ x)

theorem cycle_splice_monomial (A : Matrix α α ℝ) {u v : α} (huv : u ≠ v)
    (hrow : RowTwins A u v) (hn : 2 ≤ Fintype.card (Retain v))
    (τ : {τ : Equiv.Perm (Retain v) // SingleFullCycle τ}) :
    monomial A (cycleSpliceEquiv u v huv τ).val =
      A u v * monomial (eraseMatrix A v) τ.val :=
  splice_monomial A huv hrow τ.val (cycle_successor_ne hn τ.val τ.property _)

/-- Re-express the frozen genuine cycle sum on its genuine candidate subtype. -/
theorem cyc_eq_sum (A : Matrix α α ℝ) :
    cyc A = ∑ σ : {σ : Equiv.Perm α // SingleFullCycle σ}, monomial A σ.val := by
  unfold cyc monomial
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

end
end TripleContraction
