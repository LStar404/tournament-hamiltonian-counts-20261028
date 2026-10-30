module

public import TournamentHamiltonian.PathConvolutionGenerating

@[expose] public section

/-! Exact weighted Hamilton-cycle convolution. The cycle predicate includes
one vertex with its self-loop; for two or more vertices it is precisely a
full-support single-cycle successor permutation. No start vertex is chosen. -/
namespace WeightedCycle
open TournamentHamiltonian
open scoped BigOperators Classical
noncomputable section

/-- One complete permutation orbit, including a singleton fixed-point orbit. -/
def SingleFullCycle {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : Prop :=
  Fintype.card (CoverCycles σ) = 1

/-- Each successor permutation occurs once. The factors use the forward edge
convention `A i (σ i)`, matching `UniformBlowup.cycleWeight`. -/
def cyc {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) : ℝ :=
  ∑ σ : Equiv.Perm α, if SingleFullCycle σ then ∏ i, A i (σ i) else 0

private def invariantFullWeight {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (r : α) (σ : Equiv.Perm α)
    (f : {f : α → Bool // ∀ i, f (σ i) = f i}) : ℝ :=
  (if f.val r then
    -((-1 : ℝ) ^ Fintype.card {i : α // f.val i = true} *
      ((Equiv.Perm.sign (σ.subtypePerm (p := fun i => f.val i = true)
        (fun i => by rw [f.property i])) : ℤ) : ℝ)) else 0) * ∏ i, A (σ i) i

set_option maxHeartbeats 1000000 in
/-- Fixed-vertex marking retains every edge and cancels all other cycles.
The existing cycle-color cancellation is reused without alteration. -/
theorem marked_convolution_bool {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (r : α) :
    (∑ f : α → Bool, if f r then
      -(((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
        (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent)
      else 0) =
    ∑ σ : Equiv.Perm α, if SingleFullCycle σ then ∏ i, A (σ i) i else 0 := by
  calc
    _ = ∑ f : α → Bool, ∑ σ : {σ : Equiv.Perm α // ∀ i, f (σ i) = f i},
        invariantFullWeight A r σ.val ⟨f, σ.property⟩ := by
      apply Finset.sum_congr rfl
      intro f _
      rw [det_per_colorClass_eq_sum_preserving]
      by_cases hr : f r = true
      · rw [ite_eq_left hr, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro σ _
        simp [invariantFullWeight, hr]
      · rw [ite_eq_right hr]
        symm
        apply Finset.sum_eq_zero
        intro σ _
        simp [invariantFullWeight, hr]
    _ = ∑ x : (Σ f : α → Bool, {σ : Equiv.Perm α // ∀ i, f (σ i) = f i}),
        invariantFullWeight A r x.2.val ⟨x.1, x.2.property⟩ :=
      (Fintype.sum_sigma (fun x : (Σ f : α → Bool,
        {σ : Equiv.Perm α // ∀ i, f (σ i) = f i}) =>
          invariantFullWeight A r x.2.val ⟨x.1, x.2.property⟩)).symm
    _ = ∑ x : (Σ σ : Equiv.Perm α, {f : α → Bool // ∀ i, f (σ i) = f i}),
        invariantFullWeight A r x.1 x.2 := by
      apply Fintype.sum_equiv swapInvariantColoring
      intro x
      rfl
    _ = ∑ σ : Equiv.Perm α, ∑ f : {f : α → Bool // ∀ i, f (σ i) = f i},
        invariantFullWeight A r σ f :=
      Fintype.sum_sigma (fun x : (Σ σ : Equiv.Perm α,
        {f : α → Bool // ∀ i, f (σ i) = f i}) => invariantFullWeight A r x.1 x.2)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro σ _
      unfold invariantFullWeight
      rw [← Finset.sum_mul, sum_invariant_marked_determinant_sign]
      unfold SingleFullCycle
      split_ifs <;> simp

/-- Transposition converts the determinant's column-indexed product to
actual forward successor edges, not a second orientation count. -/
theorem marked_forward_convolution_bool {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (r : α) :
    (∑ f : α → Bool, if f r then
      -(((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det *
        (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent)
      else 0) = cyc A := by
  have h := marked_convolution_bool A.transpose r
  have hd (f : α → Bool) :
      ((-A.transpose).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det =
      ((-A).submatrix (Subtype.val : {i : α // f i = true} → α) Subtype.val).det := by
    exact Matrix.det_transpose _
  have hp (f : α → Bool) :
      (A.transpose.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent =
      (A.submatrix (Subtype.val : {i : α // f i ≠ true} → α) Subtype.val).permanent := by
    exact Matrix.permanent_transpose _
  simpa only [hd, hp, Matrix.transpose_apply, cyc] using h

/-- The exact fixed-vertex finite inclusion-exclusion identity. -/
theorem marked_convolution {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) (r : α) :
    (∑ U : Finset α, if r ∈ U then
      -(((-A).submatrix (Subtype.val : U → α) Subtype.val).det *
        (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent)
      else 0) = cyc A := by
  rw [← marked_forward_convolution_bool A r]
  apply Fintype.sum_equiv vertexSubsetEquivBool
  intro U
  let ep : {i : α // vertexSubsetEquivBool U i = true} ≃ U :=
    Equiv.subtypeEquivRight (fun i => by simp [vertexSubsetEquivBool])
  let en : {i : α // vertexSubsetEquivBool U i ≠ true} ≃ (Uᶜ : Finset α) :=
    Equiv.subtypeEquivRight (fun i => by simp [vertexSubsetEquivBool])
  have hp : ((-A).submatrix
      (Subtype.val : {i : α // vertexSubsetEquivBool U i = true} → α) Subtype.val).det =
      ((-A).submatrix (Subtype.val : U → α) Subtype.val).det :=
    Matrix.det_submatrix_equiv_self ep ((-A).submatrix (Subtype.val : U → α) Subtype.val)
  have hn : (A.submatrix
      (Subtype.val : {i : α // vertexSubsetEquivBool U i ≠ true} → α) Subtype.val).permanent =
      (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent :=
    permanent_submatrix_equiv_self
      (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val) en
  change (if r ∈ U then -_ else 0) = (if vertexSubsetEquivBool U r then -_ else 0)
  rw [hp, hn]
  simp [vertexSubsetEquivBool]

/-- The cardinality factor comes only from summing the marked vertex.
`cyc A` itself counts no cyclic starting point. The statement also holds
for the empty vertex type, where both sides are zero. -/
theorem convolution {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) :
    (Fintype.card α : ℝ) * cyc A =
      -(∑ U : Finset α, (U.card : ℝ) *
        ((-A).submatrix (Subtype.val : U → α) Subtype.val).det *
        (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent) := by
  calc
    _ = ∑ r : α, cyc A := by simp
    _ = ∑ r : α, ∑ U : Finset α, if r ∈ U then
        -(((-A).submatrix (Subtype.val : U → α) Subtype.val).det *
          (A.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent)
        else 0 := by simp_rw [marked_convolution]
    _ = _ := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro U _
      simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, Finset.univ_inter]
      ring

/-- Nonempty one-orbit condition, including the singleton case. -/
theorem singleFullCycle_iff_isCycleOn {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (σ : Equiv.Perm α) : SingleFullCycle σ ↔ σ.IsCycleOn Set.univ :=
  coverCycles_card_one_iff σ

/-- At cardinality at least two, the one-orbit condition is exactly the
full-support `IsCycle` convention used by the real blow-up model. -/
theorem singleFullCycle_iff_cycle_support {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 2 ≤ Fintype.card α) (σ : Equiv.Perm α) :
    SingleFullCycle σ ↔ σ.IsCycle ∧ σ.support = Finset.univ := by
  let : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rw [singleFullCycle_iff_isCycleOn]
  constructor
  · intro h
    refine ⟨Equiv.Perm.isCycle_iff_exists_isCycleOn.mpr
      ⟨Set.univ, Set.nontrivial_univ, h, by simp⟩, ?_⟩
    apply Finset.eq_univ_of_forall
    intro i
    exact Equiv.Perm.mem_support.mpr (h.apply_ne Set.nontrivial_univ (Set.mem_univ i))
  · rintro ⟨hc, hs⟩
    have hm : ∀ i, σ i ≠ i := fun i => Equiv.Perm.mem_support.mp (hs ▸ Finset.mem_univ i)
    have hu : {i | σ i ≠ i} = Set.univ := by ext i; simp [hm]
    simpa only [hu] using hc.isCycleOn

/-- The order-one convention is not lost through `IsCycle`, which excludes
identity permutations. The loop weight, with its sign, is retained. -/
theorem cyc_singleton (A : Matrix (Fin 1) (Fin 1) ℝ) : cyc A = A 0 0 := by
  have hσ (σ : Equiv.Perm (Fin 1)) : SingleFullCycle σ :=
    (singleFullCycle_iff_isCycleOn σ).mpr (Equiv.Perm.isCycleOn_of_subsingleton _ _)
  simp [cyc, hσ]

/-- Exact degree-`N` homogeneity for restoring the genuine weighted adjacency
from its stochastic normalization. -/
theorem cyc_smul {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℝ) (A : Matrix α α ℝ) :
    cyc (c • A) = c ^ Fintype.card α * cyc A := by
  unfold cyc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : SingleFullCycle σ <;>
    simp [h, Matrix.smul_apply, Finset.prod_mul_distrib]

/-- There is no orbit on an empty vertex type. -/
theorem cyc_empty (A : Matrix (Fin 0) (Fin 0) ℝ) : cyc A = 0 := by
  have hσ (σ : Equiv.Perm (Fin 0)) : ¬SingleFullCycle σ := by
    have he : σ = 1 := Subsingleton.elim _ _
    simp [SingleFullCycle, he]
  simp [cyc, hσ]

end
end WeightedCycle
