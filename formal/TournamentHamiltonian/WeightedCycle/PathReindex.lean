module

public import TournamentHamiltonian.PathConvolutionGenerating

@[expose] public section

namespace WeightedCycle
open scoped BigOperators
open TournamentHamiltonian
noncomputable section
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The actual all-ones-complement determinant/permanent convolution. -/
def complementConvolution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℝ :=
  ∑ U : Finset ι,
    ((Matrix.of (fun _ _ : ι => (1 : ℝ)) - A).submatrix
      (Subtype.val : U → ι) Subtype.val).det *
    (A.submatrix (Subtype.val : (Uᶜ : Finset ι) → ι) Subtype.val).permanent

/-- Reindexing every real matrix vertex leaves the finite convolution unchanged. -/
theorem complementConvolution_submatrix_equiv (e : α ≃ β) (A : Matrix β β ℝ) :
    complementConvolution (A.submatrix e e) = complementConvolution A := by
  classical
  unfold complementConvolution
  apply Fintype.sum_equiv e.finsetCongr
  intro U
  let ep : U ≃ e.finsetCongr U :=
    e.subtypeEquiv (fun i => by simp [Equiv.finsetCongr_apply])
  let en : (Uᶜ : Finset α) ≃ ((e.finsetCongr U)ᶜ : Finset β) :=
    e.subtypeEquiv (fun i => by simp [Equiv.finsetCongr_apply])
  have hp : ((Matrix.of (fun _ _ : α => (1 : ℝ)) - A.submatrix e e).submatrix
      (Subtype.val : U → α) Subtype.val).det =
      ((Matrix.of (fun _ _ : β => (1 : ℝ)) - A).submatrix
        (Subtype.val : e.finsetCongr U → β) Subtype.val).det :=
    Matrix.det_submatrix_equiv_self ep
      ((Matrix.of (fun _ _ : β => (1 : ℝ)) - A).submatrix
        (Subtype.val : e.finsetCongr U → β) Subtype.val)
  have hn : ((A.submatrix e e).submatrix
      (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent =
      (A.submatrix (Subtype.val : ((e.finsetCongr U)ᶜ : Finset β) → β)
        Subtype.val).permanent :=
    permanent_submatrix_equiv_self
      (A.submatrix (Subtype.val : ((e.finsetCongr U)ᶜ : Finset β) → β) Subtype.val) en
  rw [hp, hn]

end
end WeightedCycle
