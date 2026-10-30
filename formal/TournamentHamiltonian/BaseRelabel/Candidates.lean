module

public import TournamentHamiltonian.BaseRelabel.Samples

@[expose] public section

set_option autoImplicit false
namespace BaseRelabel
open TournamentHamiltonian UniformBlowup RegularOrientation
noncomputable section

/-- Relabel all vertices of an actual Hamilton path candidate. -/
def arrangementEquiv {d m : ℕ} (e : Equiv.Perm (Fin d)) :
    Equiv.Perm (Arrangement d m) where
  toFun π := π.trans (vertexEquiv e)
  invFun π := π.trans (vertexEquiv e).symm
  left_inv π := by apply Equiv.ext; intro i; simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  right_inv π := by apply Equiv.ext; intro i; simp only [Equiv.trans_apply, Equiv.apply_symm_apply]

/-- Full-support successor permutations are transported by conjugation. -/
def cycleEquiv {d m : ℕ} (e : Equiv.Perm (Fin d)) : Equiv.Perm (Cycle d m) where
  toFun σ := ⟨vertexEquiv e * σ.val * (vertexEquiv e)⁻¹,
    σ.property.1.conj, by simp [Equiv.Perm.support_conj, σ.property.2]⟩
  invFun σ := ⟨(vertexEquiv e)⁻¹ * σ.val * vertexEquiv e,
    by simpa using σ.property.1.conj (g := (vertexEquiv e)⁻¹),
    by simpa [σ.property.2] using
      (Equiv.Perm.support_conj (σ := (vertexEquiv e)⁻¹) (τ := σ.val))⟩
  left_inv σ := by apply Subtype.ext; simp [mul_assoc]
  right_inv σ := by apply Subtype.ext; simp [mul_assoc]

@[simp] theorem cycleEquiv_apply_vertex {d m : ℕ} (e : Equiv.Perm (Fin d))
    (σ : Cycle d m) (u : Vertex d m) :
    (cycleEquiv e σ).val (vertexEquiv e u) = vertexEquiv e (σ.val u) := by
  change (vertexEquiv e) (σ.val ((vertexEquiv e).symm ((vertexEquiv e) u))) = _
  rw [Equiv.symm_apply_apply]

theorem isPath_relabel {d m : ℕ} (T : Tournament d) (e : Equiv.Perm (Fin d))
    (ω : Sample d m) (π : Arrangement d m) :
    IsPath (relabelTournament T e) ω π ↔
      IsPath T (sampleEquiv e ω) (arrangementEquiv e π) := by
  unfold IsPath tail head
  simp only [arc_relabel, arrangementEquiv, Equiv.coe_fn_mk, Equiv.trans_apply]

theorem isCyclePresent_relabel {d m : ℕ} (T : Tournament d)
    (e : Equiv.Perm (Fin d)) (ω : Sample d m) (σ : Cycle d m) :
    IsCyclePresent (relabelTournament T e) ω σ ↔
      IsCyclePresent T (sampleEquiv e ω) (cycleEquiv e σ) := by
  constructor
  · intro h u
    obtain ⟨v, rfl⟩ := (vertexEquiv e).surjective u
    rw [cycleEquiv_apply_vertex, ← arc_relabel]
    exact h v
  · intro h u
    rw [arc_relabel, ← cycleEquiv_apply_vertex]
    exact h (vertexEquiv e u)

/-- Counts agree samplewise through an explicit bijection, with no size guard. -/
theorem pathCount_relabel {d m : ℕ} (T : Tournament d) (e : Equiv.Perm (Fin d))
    (ω : Sample d m) :
    UniformBlowup.pathCount (relabelTournament T e) ω =
      UniformBlowup.pathCount T (sampleEquiv e ω) := by
  classical
  unfold UniformBlowup.pathCount
  apply Finset.card_bij (fun π _ => arrangementEquiv e π)
  · intro π hπ
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ← isPath_relabel] using hπ
  · intro π _ ρ _ h
    exact (arrangementEquiv e).injective h
  · intro π hπ
    refine ⟨(arrangementEquiv e).symm π, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, isPath_relabel,
      Equiv.apply_symm_apply] using hπ

theorem cycleCount_relabel {d m : ℕ} (T : Tournament d) (e : Equiv.Perm (Fin d))
    (ω : Sample d m) :
    cycleCount (relabelTournament T e) ω = cycleCount T (sampleEquiv e ω) := by
  classical
  unfold cycleCount
  apply Finset.card_bij (fun σ _ => cycleEquiv e σ)
  · intro σ hσ
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ← isCyclePresent_relabel] using hσ
  · intro σ _ τ _ h
    exact (cycleEquiv e).injective h
  · intro σ hσ
    refine ⟨(cycleEquiv e).symm σ, ?_, by simp⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, isCyclePresent_relabel,
      Equiv.apply_symm_apply] using hσ

end
end BaseRelabel
