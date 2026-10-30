module

public import TournamentHamiltonian.BlockMotif.Regular

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BlockMotif
open TripleContraction FiniteMotif ForestGaussian TournamentHamiltonian
open RegularOrientation UniformBlowup
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m k : ℕ}

def nativeArrangement (π : Ordering (Fin (d*m))) : Arrangement d m :=
  ((finCongr (Fintype.card_fin (d*m)).symm).trans π).trans finProdFinEquiv.symm

def nativeCycle (hN : 3≤d*m) (σ : Full (Fin (d*m))) : Cycle d m := by
  letI : Nonempty (Fin (d*m)) := ⟨⟨0,by omega⟩⟩
  let τ := fullCongr finProdFinEquiv.symm σ
  exact ⟨τ.val,(WeightedCycle.singleFullCycle_iff_cycle_support (by simpa using (show 2≤d*m by omega)) τ.val).mp τ.property⟩

/-- The index normalization is an actual equivalence of all path orderings. -/
def nativeArrangementEquiv : Ordering (Fin (d*m)) ≃ Arrangement d m :=
  Equiv.equivCongr (finCongr (Fintype.card_fin (d*m))) finProdFinEquiv.symm

@[simp] theorem nativeArrangementEquiv_apply (π : Ordering (Fin (d*m))) :
    nativeArrangementEquiv π=nativeArrangement π := rfl

/-- Reindexing is bijective on unrooted cycles, not just an injection. -/
def nativeCycleEquiv (hN : 3≤d*m) : Full (Fin (d*m)) ≃ Cycle d m := by
  letI : Nonempty (Fin (d*m)) := ⟨⟨0,by omega⟩⟩
  exact (fullCongr finProdFinEquiv.symm).trans (Equiv.subtypeEquivRight
    (fun τ => WeightedCycle.singleFullCycle_iff_cycle_support (by simpa using (show 2≤d*m by omega)) τ))

@[simp] theorem nativeCycleEquiv_apply (hN : 3≤d*m) (σ : Full (Fin (d*m))) :
    nativeCycleEquiv hN σ=nativeCycle hN σ := rfl

@[simp] theorem nativeCycle_apply (hN : 3≤d*m) (σ : Full (Fin (d*m))) (v : Vertex d m) :
    (nativeCycle hN σ).val v=finProdFinEquiv.symm (σ.val (finProdFinEquiv v)) := rfl

theorem cycle_contained_iff (hN : 3≤d*m) (σ : Full (Fin (d*m))) (S : Tournament (d*m)) :
    Contained (cycleSystem hN σ) S ↔ ∀u,S.val u (σ.val u)=true := by
  constructor
  · intro h u; exact h u (σ.val u) rfl
  · intro h u v huv; exact huv ▸ h u

theorem path_contained_iff (π : Ordering (Fin (d*m))) (S : Tournament (d*m)) :
    Contained (pathSystem π) S ↔ ∀r : Step (Fintype.card (Fin (d*m))), S.val (π r.val.1) (π r.val.2)=true := by
  constructor
  · intro h r; exact h _ _ ⟨r,rfl,rfl⟩
  · intro h u v huv
    obtain ⟨r,hu,hv⟩ := huv
    rw [←hu,←hv]
    exact h r

/-- This is the preexisting actual cycle-presence predicate, with no root multiplier. -/
theorem regular_cycle_native (hN : 3≤d*(2*k+1)) (σ : Full (Fin (d*(2*k+1))))
    (T : Tournament d) (ω : RegularSample d k) :
    Contained (cycleSystem hN σ) (regularBlowup T ω finProdFinEquiv.symm) ↔
      IsCyclePresent T (regularSampleBits ω) (nativeCycle hN σ) := by
  rw [cycle_contained_iff]
  constructor
  · intro h v
    have hh := h (finProdFinEquiv v)
    simpa only [regularBlowup,blowup,Equiv.symm_apply_apply,nativeCycle_apply] using hh
  · intro h u
    have hh := h (finProdFinEquiv.symm u)
    simpa only [nativeCycle_apply,Equiv.apply_symm_apply,regularBlowup,blowup] using hh

theorem step_forall_cast {n n' : ℕ} (h : n=n') (P : Fin n → Fin n → Prop) :
    (∀r : Step n,P r.val.1 r.val.2) ↔
      ∀r : Step n',P ((finCongr h).symm r.val.1) ((finCongr h).symm r.val.2) := by
  subst n'
  rfl

/-- The old actual path predicate uses exactly the same non-wrapping steps, also for N=0,1. -/
theorem regular_path_native (π : Ordering (Fin (d*(2*k+1))))
    (T : Tournament d) (ω : RegularSample d k) :
    Contained (pathSystem π) (regularBlowup T ω finProdFinEquiv.symm) ↔
      IsPath T (regularSampleBits ω) (nativeArrangement π) := by
  rw [path_contained_iff]
  simpa only [IsPath,tail,head,nativeArrangement,regularBlowup,blowup,Equiv.trans_apply,finCongr_symm] using
    step_forall_cast (Fintype.card_fin (d*(2*k+1)))
      (fun i j => UniformBlowup.arc T (regularSampleBits ω) (finProdFinEquiv.symm (π i)) (finProdFinEquiv.symm (π j))=true)

end
end BlockMotif
