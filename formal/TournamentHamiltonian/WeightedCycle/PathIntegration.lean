module

public import TournamentHamiltonian.UniformBlowup.Normalization
public import TournamentHamiltonian.PathConvolutionGenerating
public import TournamentHamiltonian.WeightedCycle.PathMainTerm
public import TournamentHamiltonian.WeightedCycle.PathReindex

@[expose] public section

/-! Genuine linear-order path sums and their exact finite convolution. -/
namespace WeightedCycle
open TournamentHamiltonian
open scoped BigOperators Classical
noncomputable section

/-- All linear arrangements, with consecutive edges only and no wrap-around. -/
def linearPathSum {α : Type*} [Fintype α] [DecidableEq α] (n : ℕ) (A : Matrix α α ℝ) : ℝ :=
  ∑ e : Fin n ≃ α, ∏ r : UniformBlowup.Step n, A (e r.val.1) (e r.val.2)

/-- Canonical genuine weighted path count on an arbitrary finite vertex type. -/
def path {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) : ℝ :=
  linearPathSum (Fintype.card α) A

/-- Fin-indexed paths are actual permutation orderings. -/
def finPath {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ r : UniformBlowup.Step n, A (σ r.val.1) (σ r.val.2)

def orderingEquiv {α : Type*} {n : ℕ} (e : Fin n ≃ α) :
    Equiv.Perm (Fin n) ≃ (Fin n ≃ α) where
  toFun σ := σ.trans e
  invFun π := π.trans e.symm
  left_inv σ := by apply Equiv.ext; intro i; exact e.symm_apply_apply (σ i)
  right_inv π := by apply Equiv.ext; intro i; exact e.apply_symm_apply (π i)

theorem linearPathSum_eq_finPath {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (A : Matrix α α ℝ) (e : Fin n ≃ α) :
    linearPathSum n A = finPath (A.submatrix e e) := by
  symm
  apply Fintype.sum_equiv (orderingEquiv e)
  intro σ
  rfl

def consecutiveStepEquiv (n : ℕ) : UniformBlowup.Step (n+1) ≃ Fin n where
  toFun r := ⟨r.val.1.val, by have := r.val.2.isLt; have := r.property; omega⟩
  invFun i := ⟨(i.castSucc, i.succ), rfl⟩
  left_inv r := by
    apply Subtype.ext
    apply Prod.ext
    · exact Fin.ext rfl
    · exact Fin.ext r.property.symm
  right_inv i := rfl

theorem finPath_succ_eq {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    finPath A = ∑ σ : Equiv.Perm (Fin (n+1)),
      ∏ i : Fin n, A (σ i.castSucc) (σ i.succ) := by
  apply Finset.sum_congr rfl
  intro σ _
  apply Fintype.prod_equiv (consecutiveStepEquiv n)
  intro r
  congr 2
  exact Fin.ext r.property

/-- The generic complement is `J-A`, never `I+A` for a general matrix. -/
theorem finPath_convolution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    finPath A = ∑ U : Finset (Fin n),
      ((Matrix.of (fun _ _ => (1 : ℝ)) - A).submatrix
        (Subtype.val : U → Fin n) Subtype.val).det *
      (A.submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n) Subtype.val).permanent := by
  rw [det_per_subset_sum_eq_bool, complement_det_per_convolution_bool_eq_cycles]
  cases n with
  | zero =>
      have : IsEmpty (UniformBlowup.Step 0) := ⟨fun r => Fin.elim0 r.val.1⟩
      simp [finPath]
  | succ n =>
      rw [finPath_succ_eq, sum_path_products_eq_marked_cycles]
      simp

/-- Every finite real matrix: actual linear arrangements, not an abstract
surrogate, equal the complement determinant/permanent convolution. -/
theorem path_convolution {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α ℝ) : path A = complementConvolution A := by
  unfold path
  rw [linearPathSum_eq_finPath A (Fintype.equivFin α).symm, finPath_convolution]
  exact complementConvolution_submatrix_equiv (Fintype.equivFin α).symm A

/-- The canonical path definition agrees exactly with the real model's
arrangement sum. Unlike cycles, the expectation identity needs no N≥3 cutoff. -/
theorem path_eq_uniform_weightedPathSum {d m : ℕ} (T : Tournament d) :
    path (UniformBlowup.weight (m := m) T) = UniformBlowup.weightedPathSum (m := m) T := by
  change linearPathSum (Fintype.card (Fin d × Fin m)) _ = _
  simp only [Fintype.card_prod, Fintype.card_fin]
  rfl

theorem path_eq_uniform_avgPath {d m : ℕ} (T : Tournament d) :
    path (UniformBlowup.weight (m := m) T) = UniformBlowup.avgPath (m := m) T := by
  rw [UniformBlowup.avgPath_eq_weightedPathSum, path_eq_uniform_weightedPathSum]

/-- Direct finite determinant/permanent formula for the actual uniform-model
path expectation, valid also for empty/singleton/2-vertex models. -/
theorem uniform_avgPath_convolution {d m : ℕ} (T : Tournament d) :
    UniformBlowup.avgPath (m := m) T =
      complementConvolution (UniformBlowup.weight (m := m) T) := by
  exact (path_eq_uniform_avgPath (m := m) T).symm.trans
    (path_convolution (UniformBlowup.weight (m := m) T))

/-- Exact minor-ratio error for normalized true paths. No minor-ratio estimate
or convergence statement is assumed. Division is algebraically totalized. -/
theorem normalized_path_error {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (D : Matrix α α ℝ) (hrow : ∀ i, ∑ j, D i j = 1) :
    path D / ((Fintype.card α : ℝ) * D.permanent) - (1 - centered D).det =
      (∑ U : Finset α,
        ((Matrix.of (fun _ _ : α => (1 : ℝ)) - D).submatrix
          (Subtype.val : U → α) Subtype.val).det *
        ((D.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent /
          D.permanent - 1)) / (Fintype.card α : ℝ) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : (1 - centered D).det =
      (∑ U : Finset α,
        ((Matrix.of (fun _ _ : α => (1 : ℝ)) - D).submatrix
          (Subtype.val : U → α) Subtype.val).det) / (Fintype.card α : ℝ) := by
    rw [path_main_term_eq_card_mul_centered_det D hrow]
    field_simp
  rw [path_convolution, hd]
  unfold complementConvolution
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, sub_div]
  congr 1
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro U _
  ring

/-- Finite triangle inequality with precisely the correct `1/N` prefactor. -/
theorem abs_normalized_path_error_le {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (D : Matrix α α ℝ) (hrow : ∀ i, ∑ j, D i j = 1) :
    |path D / ((Fintype.card α : ℝ) * D.permanent) - (1 - centered D).det| ≤
      (∑ U : Finset α,
        |((Matrix.of (fun _ _ : α => (1 : ℝ)) - D).submatrix
          (Subtype.val : U → α) Subtype.val).det| *
        |(D.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent /
          D.permanent - 1|) / (Fintype.card α : ℝ) := by
  rw [normalized_path_error D hrow, abs_div, Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
    (fun U : Finset α =>
      ((Matrix.of (fun _ _ : α => (1 : ℝ)) - D).submatrix
        (Subtype.val : U → α) Subtype.val).det *
      ((D.submatrix (Subtype.val : (Uᶜ : Finset α) → α) Subtype.val).permanent /
        D.permanent - 1)) Finset.univ

/-- A singleton path has no edges, independently of the matrix's diagonal. -/
theorem path_singleton (A : Matrix (Fin 1) (Fin 1) ℝ) : path A = 1 := by
  have : IsEmpty (UniformBlowup.Step 1) := ⟨fun r => by
    have h₁ := r.val.1.isLt
    have h₂ := r.val.2.isLt
    have hr := r.property
    omega⟩
  change linearPathSum 1 A = 1
  rw [linearPathSum_eq_finPath A (Equiv.refl _)]
  simp [finPath]

/-- The empty ordering is a single edge-free path. -/
theorem path_empty (A : Matrix (Fin 0) (Fin 0) ℝ) : path A = 1 := by
  have : IsEmpty (UniformBlowup.Step 0) := ⟨fun r => Fin.elim0 r.val.1⟩
  change linearPathSum 0 A = 1
  rw [linearPathSum_eq_finPath A (Equiv.refl _)]
  simp [finPath]

/-- Exact degree N−1 homogeneity; the empty path is handled by the same
empty-product convention. -/
theorem path_smul {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℝ) (A : Matrix α α ℝ) :
    path (c • A) = c ^ (Fintype.card α - 1) * path A := by
  unfold path linearPathSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp [Matrix.smul_apply, Finset.prod_mul_distrib, UniformBlowup.card_step]

end
end WeightedCycle
