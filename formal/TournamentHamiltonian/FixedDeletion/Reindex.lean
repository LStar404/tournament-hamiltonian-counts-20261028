module

public import TournamentHamiltonian.DensePathConvergence

@[expose] public section

set_option autoImplicit false
namespace FixedDeletion
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

def liftSet (U : Finset α) (V : Finset (Uᶜ : Finset α)) : Finset α :=
  V.map (Function.Embedding.subtype _)

@[simp] theorem mem_liftSet (U : Finset α) (V : Finset (Uᶜ : Finset α)) (x : (Uᶜ : Finset α)) :
    x.val ∈ liftSet U V ↔ x ∈ V := by
  simp [liftSet]

@[simp] theorem card_liftSet (U : Finset α) (V : Finset (Uᶜ : Finset α)) :
    (liftSet U V).card = V.card := Finset.card_map _

theorem disjoint_liftSet (U : Finset α) (V : Finset (Uᶜ : Finset α)) : Disjoint U (liftSet U V) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hy
  exact (Finset.mem_compl.mp y.property) hx

/-- Actual retained subsets are exactly the ambient subsets disjoint from U. -/
def subsetEquiv (U : Finset α) :
    Finset (Uᶜ : Finset α) ≃ {V : Finset α // Disjoint U V} where
  toFun V := ⟨liftSet U V, disjoint_liftSet U V⟩
  invFun V := V.val.subtype (fun x => x ∈ Uᶜ)
  left_inv V := by ext x; simp
  right_inv V := by
    apply Subtype.ext
    ext x
    simp only [liftSet, Finset.mem_map, Function.Embedding.subtype_apply, Finset.mem_subtype]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hx
      have hxu : x ∈ Uᶜ := Finset.mem_compl.mpr (fun hu => Finset.disjoint_left.mp V.property hu hx)
      exact ⟨⟨x,hxu⟩,hx,rfl⟩

def selectedEquiv (U : Finset α) (V : Finset (Uᶜ : Finset α)) : V ≃ liftSet U V :=
  Equiv.ofBijective (fun x => ⟨x.val.val, (mem_liftSet U V x.val).mpr x.property⟩) (by
    constructor
    · intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : liftSet U V => z.val) h))
    · intro y
      obtain ⟨x,hx,hxy⟩ := Finset.mem_map.mp y.property
      exact ⟨⟨x,hx⟩, Subtype.ext hxy⟩)

/-- Complement inside the retained vertices is genuinely ambient deletion U∪V. -/
def complementEquiv (U : Finset α) (V : Finset (Uᶜ : Finset α)) :
    (Vᶜ : Finset (Uᶜ : Finset α)) ≃ ((U ∪ liftSet U V)ᶜ : Finset α) where
  toFun x := ⟨x.val.val, by
    simp only [Finset.mem_compl, Finset.mem_union, not_or]
    exact ⟨Finset.mem_compl.mp x.val.property,
      fun h => (Finset.mem_compl.mp x.property) ((mem_liftSet U V x.val).mp h)⟩⟩
  invFun x := ⟨⟨x.val, by
    have h := Finset.mem_compl.mp x.property
    exact Finset.mem_compl.mpr (fun hU => h (Finset.mem_union_left _ hU))⟩, by
    apply Finset.mem_compl.mpr
    intro hV
    exact (Finset.mem_compl.mp x.property)
      (Finset.mem_union_right _ ((mem_liftSet U V _).mpr hV))⟩
  left_inv _ := rfl
  right_inv _ := rfl

def principal (D : Matrix α α ℝ) (U : Finset α) :
    Matrix (Uᶜ : Finset α) (Uᶜ : Finset α) ℝ := D.submatrix Subtype.val Subtype.val

def cycleCoeff (D : Matrix α α ℝ) (V : Finset α) : ℝ :=
  -(V.card : ℝ)*((-D).submatrix (Subtype.val : V → α) Subtype.val).det

def pathCoeff (D : Matrix α α ℝ) (V : Finset α) : ℝ :=
  ((Matrix.of (fun _ _ : α => (1 : ℝ))-D).submatrix (Subtype.val : V → α) Subtype.val).det

@[simp] theorem principal_fin {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (U : Finset (Fin n)) :
    principal D U = densePrincipalMinor D U := rfl

theorem principal_nested_permanent (D : Matrix α α ℝ) (U : Finset α)
    (V : Finset (Uᶜ : Finset α)) :
    (principal (principal D U) V).permanent = (principal D (U ∪ liftSet U V)).permanent := by
  exact permanent_submatrix_equiv_self (principal D (U ∪ liftSet U V)) (complementEquiv U V)

theorem cycleCoeff_lift (D : Matrix α α ℝ) (U : Finset α)
    (V : Finset (Uᶜ : Finset α)) : cycleCoeff (principal D U) V = cycleCoeff D (liftSet U V) := by
  unfold cycleCoeff
  rw [card_liftSet]
  congr 1
  exact Matrix.det_submatrix_equiv_self (selectedEquiv U V)
    ((-D).submatrix (Subtype.val : liftSet U V → α) Subtype.val)

theorem pathCoeff_lift (D : Matrix α α ℝ) (U : Finset α)
    (V : Finset (Uᶜ : Finset α)) : pathCoeff (principal D U) V = pathCoeff D (liftSet U V) := by
  exact Matrix.det_submatrix_equiv_self (selectedEquiv U V)
    ((Matrix.of (fun _ _ : α => (1 : ℝ))-D).submatrix
      (Subtype.val : liftSet U V → α) Subtype.val)

theorem cycle_convolution (D : Matrix α α ℝ) :
    (Fintype.card α : ℝ)*WeightedCycle.cyc D = ∑ V : Finset α, cycleCoeff D V*(principal D V).permanent := by
  rw [WeightedCycle.convolution, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro V _
  simp only [cycleCoeff, principal]
  ring

theorem path_convolution (D : Matrix α α ℝ) :
    WeightedCycle.path D = ∑ V : Finset α, pathCoeff D V*(principal D V).permanent :=
  WeightedCycle.path_convolution D

theorem deleted_cycle_convolution (D : Matrix α α ℝ) (U : Finset α) :
    (Fintype.card (Uᶜ : Finset α) : ℝ)*WeightedCycle.cyc (principal D U) =
      ∑ V : {V : Finset α // Disjoint U V}, cycleCoeff D V.val*(principal D (U∪V.val)).permanent := by
  rw [cycle_convolution]
  apply Fintype.sum_equiv (subsetEquiv U)
  intro V
  rw [cycleCoeff_lift, principal_nested_permanent]
  rfl

theorem deleted_path_convolution (D : Matrix α α ℝ) (U : Finset α) :
    WeightedCycle.path (principal D U) =
      ∑ V : {V : Finset α // Disjoint U V}, pathCoeff D V.val*(principal D (U∪V.val)).permanent := by
  rw [path_convolution]
  apply Fintype.sum_equiv (subsetEquiv U)
  intro V
  rw [pathCoeff_lift, principal_nested_permanent]
  rfl

end
end FixedDeletion
