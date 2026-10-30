module

public import TournamentHamiltonian.TripleContraction.Sentinel

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace TripleContraction
open TournamentHamiltonian WeightedCycle UniformBlowup
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]

def linearMonomial {n : ℕ} (A : Matrix α α ℝ) (π : Fin n ≃ α) : ℝ :=
  ∏ r : Step n, A (π r.val.1) (π r.val.2)

abbrev pathMonomial (A : Matrix α α ℝ) (π : Ordering α) := linearMonomial A π

def extendLinear {n : ℕ} (π : Fin n ≃ α) : Fin (n+1) ≃ Option α :=
  (finSuccEquiv n).trans (Equiv.optionCongr π)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem extendLinear_zero {n : ℕ} (π : Fin n ≃ α) : extendLinear π 0=none := by
  simp [extendLinear]
omit [Fintype α] [DecidableEq α] in
@[simp] theorem extendLinear_succ {n : ℕ} (π : Fin n ≃ α) (i : Fin n) :
    extendLinear π i.succ=some (π i) := by simp [extendLinear]

omit [Fintype α] [DecidableEq α] in
theorem linearMonomial_succ {n : ℕ} (A : Matrix α α ℝ) (π : Fin (n+1) ≃ α) :
    linearMonomial A π = ∏ i : Fin n, A (π i.castSucc) (π i.succ) := by
  apply Fintype.prod_equiv (consecutiveStepEquiv n)
  intro r
  congr 2
  exact Fin.ext r.property

omit [DecidableEq α] in
/-- Every old edge is retained once; the two sentinel factors are exactly one.
The n=0 branch uses its sentinel loop of weight one. -/
theorem sentinel_rotation_monomial {n : ℕ} (A : Matrix α α ℝ) (π : Fin n ≃ α) :
    monomial (sentinel A) ((extendLinear π).permCongr (finRotate (n+1))) = linearMonomial A π := by
  rw [monomial_congr]
  change (∏ i : Fin (n+1), sentinel A (extendLinear π i) (extendLinear π (finRotate (n+1) i))) = _
  cases n with
  | zero =>
    let : IsEmpty (Step 0) := ⟨fun r => Fin.elim0 r.val.1⟩
    simp [linearMonomial,sentinel,extendLinear]
  | succ n =>
    rw [linearMonomial_succ,Fin.prod_univ_castSucc]
    simp only [finRotate_castSucc,finRotate_last]
    rw [Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero,extendLinear_zero,extendLinear_succ,sentinel_none_left,sentinel_none_right,sentinel_some,
      one_mul,mul_one,← Fin.succ_castSucc]

theorem orderingCycleEquiv_monomial (A : Matrix α α ℝ) (π : Ordering α) :
    monomial (sentinel A) (orderingCycleEquiv π).val = pathMonomial A π := by
  rw [orderingCycleEquiv_val]
  exact sentinel_rotation_monomial A π

/-- Genuine ordered consecutive edge, not a wrap-around relation. -/
def PathArc (π : Ordering α) (u v : α) : Prop :=
  ∃ r : Step (Fintype.card α), π r.val.1=u ∧ π r.val.2=v

omit [Fintype α] [DecidableEq α] in
theorem rotate_succ_iff {n : ℕ} (i j : Fin n) :
    finRotate (n+1) i.succ=j.succ ↔ j.val=i.val+1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [show (Fin.last n).succ=Fin.last (n+1) from rfl,finRotate_last]
      constructor
      · intro h
        exact False.elim (Fin.succ_ne_zero j h.symm)
      · intro h
        have := j.isLt
        simp only [Fin.val_last] at h
        omega
    · rw [Fin.succ_castSucc,finRotate_castSucc]
      constructor
      · intro h
        have he := Fin.succ_injective _ h
        exact congrArg Fin.val he.symm
      · intro h
        congr 1
        apply Fin.ext
        exact h.symm

/-- The sentinel prevents the last-to-first closure from becoming a path arc. -/
theorem orderingCycleEquiv_arc (π : Ordering α) (u v : α) :
    (orderingCycleEquiv π).val (some u)=some v ↔ PathArc π u v := by
  have he : (orderingCycleEquiv π).val (some u)=some v ↔
      finRotate (Fintype.card α+1) (π.symm u).succ=(π.symm v).succ := by
    have hu : extendOrder π (π.symm u).succ=some u := by simp
    have hv : extendOrder π (π.symm v).succ=some v := by simp
    rw [← hu, ← hv]
    simp only [orderingCycleEquiv_rotate,Equiv.apply_eq_iff_eq]
  rw [he,rotate_succ_iff]
  constructor
  · intro h
    exact ⟨⟨(π.symm u,π.symm v),h⟩,π.apply_symm_apply u,π.apply_symm_apply v⟩
  · rintro ⟨r,hu,hv⟩
    rw [← hu,← hv,π.symm_apply_apply,π.symm_apply_apply]
    exact r.property

/-- The exact total weighted path sum, also on empty and singleton vertex sets. -/
theorem sentinel_cyc_eq_path (A : Matrix α α ℝ) : cyc (sentinel A)=path A := by
  rw [cyc_eq_sum]
  change (∑ σ : Full (Option α), monomial (sentinel A) σ.val) = ∑ π : Ordering α, pathMonomial A π
  symm
  apply Fintype.sum_equiv orderingCycleEquiv
  intro π
  exact (orderingCycleEquiv_monomial A π).symm

end
end TripleContraction
