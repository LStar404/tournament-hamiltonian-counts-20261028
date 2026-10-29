module

public import Tournament.SignMatrix
public import TournamentHamiltonian.PathConvolutionGenerating

/-!
# Exact finite Hamilton path convolution

The cycle-cancellation proof is reused from the pinned legacy source listed
in `CONVOLUTION_SOURCE.json`. Only the interfaces are proved here. No
regularity, positivity of the order, or asymptotic assumption is needed.
The empty ordering counts as one Hamilton path.
-/

@[expose] public section

namespace TournamentPaths

/-- Preserve every Boolean edge when changing to the legacy tournament type. -/
def toLegacy {n : ℕ} (T : Tournament (Fin n)) :
    TournamentHamiltonian.Tournament n :=
  ⟨T.edge, T.loopless, T.oriented⟩

/-- A Hamilton ordering for every order, including zero. -/
def IsHamiltonPathFinite {n : ℕ} (T : Tournament (Fin n))
    (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → T.edge (p i) (p j) = true

/-- Count actual vertex orderings; no quotient by reversal is taken. -/
noncomputable def pathCountFinite {n : ℕ} (T : Tournament (Fin n)) : ℕ := by
  classical
  exact ∑ p : Equiv.Perm (Fin n), if IsHamiltonPathFinite T p then 1 else 0

theorem isHamiltonPathFinite_iff_legacy {n : ℕ} (T : Tournament (Fin n))
    (p : Equiv.Perm (Fin n)) :
    IsHamiltonPathFinite T p ↔ TournamentHamiltonian.IsHamiltonian (toLegacy T) p :=
  Iff.rfl

/-- The all-orders predicate agrees with the original consecutive-edge predicate. -/
theorem isHamiltonPathFinite_iff {n : ℕ} (T : Tournament (Fin (n + 1)))
    (p : Equiv.Perm (Fin (n + 1))) :
    IsHamiltonPathFinite T p ↔ IsHamiltonPath T p :=
  TournamentHamiltonian.isHamiltonian_iff_consecutive (toLegacy T) p

theorem pathCountFinite_eq_legacy {n : ℕ} (T : Tournament (Fin n)) :
    pathCountFinite T = TournamentHamiltonian.pathCount (toLegacy T) := by
  classical
  unfold pathCountFinite TournamentHamiltonian.pathCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

/-- Exact agreement with the path count already used by the new manuscript. -/
theorem pathCountFinite_eq_pathCount {n : ℕ} (T : Tournament (Fin (n + 1))) :
    pathCountFinite T = pathCount T := by
  classical
  unfold pathCountFinite pathCount
  apply Finset.sum_congr rfl
  intro p _
  rw [isHamiltonPathFinite_iff]

theorem adjacency_toLegacy {n : ℕ} (T : Tournament (Fin n)) :
    TournamentHamiltonian.adjacency (toLegacy T) = adjacency T := by
  rfl

/-- The principal matrix is precisely the identity plus restricted adjacency. -/
noncomputable def pathPrincipalMatrix {n : ℕ} (T : Tournament (Fin n))
    (U : Finset (Fin n)) : Matrix U U ℝ :=
  1 + (adjacency T).submatrix Subtype.val Subtype.val

theorem principalWeightMatrix_toLegacy {n : ℕ} (T : Tournament (Fin n))
    (U : Finset (Fin n)) :
    TournamentHamiltonian.principalWeightMatrix (toLegacy T) U =
      pathPrincipalMatrix T U := by
  rfl

/-- The manuscript's determinant--permanent sum, defined independently of counts. -/
noncomputable def pathConvolutionSum {n : ℕ} (T : Tournament (Fin n)) : ℝ :=
  ∑ U : Finset (Fin n), (pathPrincipalMatrix T U).det *
    ((adjacency T).submatrix (Subtype.val : (Uᶜ : Finset (Fin n)) → Fin n)
      Subtype.val).permanent

theorem pathConvolutionSum_eq_legacy {n : ℕ} (T : Tournament (Fin n)) :
    pathConvolutionSum T = TournamentHamiltonian.pathConvolutionSum (toLegacy T) := by
  rfl

/-- Exact convolution for actual tournaments of every finite order. -/
theorem pathCountFinite_eq_pathConvolutionSum {n : ℕ} (T : Tournament (Fin n)) :
    (pathCountFinite T : ℝ) = pathConvolutionSum T := by
  rw [pathCountFinite_eq_legacy, pathConvolutionSum_eq_legacy]
  exact TournamentHamiltonian.pathCount_eq_pathConvolutionSum (toLegacy T)

/-- Exact convolution for the existing, genuine nonempty Hamilton path count. -/
theorem pathCount_eq_pathConvolutionSum {n : ℕ} (T : Tournament (Fin (n + 1))) :
    (pathCount T : ℝ) = pathConvolutionSum T := by
  rw [← pathCountFinite_eq_pathCount]
  exact pathCountFinite_eq_pathConvolutionSum T

/-- Explicit principal-submatrix formula in the new tournament model. -/
theorem pathCount_eq_positive_convolution {n : ℕ} (T : Tournament (Fin (n + 1))) :
    (pathCount T : ℝ) = ∑ U : Finset (Fin (n + 1)),
      (1 + (adjacency T).submatrix (Subtype.val : U → Fin (n + 1))
        Subtype.val).det *
      ((adjacency T).submatrix
        (Subtype.val : (Uᶜ : Finset (Fin (n + 1))) → Fin (n + 1))
        Subtype.val).permanent :=
  pathCount_eq_pathConvolutionSum T

/-- The unique empty vertex ordering has no edge constraints. -/
theorem empty_path_count (T : Tournament (Fin 0)) : pathCountFinite T = 1 := by
  simp [pathCountFinite, IsHamiltonPathFinite]

theorem empty_path_convolution (T : Tournament (Fin 0)) : pathConvolutionSum T = 1 := by
  rw [← pathCountFinite_eq_pathConvolutionSum, empty_path_count]
  norm_num

theorem singleton_path_convolution (T : Tournament (Fin 1)) :
    pathConvolutionSum T = 1 := by
  rw [← pathCount_eq_pathConvolutionSum, one_vertex_path_count]
  norm_num

end TournamentPaths
