module

public import TournamentHamiltonian.Equality.PivotClassification

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

/-- A strict total tournament order on a finite set can be enumerated in order.
The conclusion uses the pre-existing `transitiveSkew`, not a newly assumed model. -/
theorem exists_relabel_eq_transitive_of_strictTotalOrder {ι : Type*} [Fintype ι]
    {n : ℕ} (hcard : Fintype.card ι = n) {S : Matrix ι ι ℝ} (hS : IsSkewSign S)
    (hsto : IsStrictTotalOrder ι (fun i j => S i j = 1)) :
    ∃ e : Fin n ≃ ι, S.submatrix e e = (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  let := hsto
  let : LinearOrder ι := linearOrderOfSTO (fun i j => S i j = 1)
  let e := Fintype.orderIsoFinOfCardEq ι hcard
  refine ⟨e.toEquiv, ?_⟩
  ext i j
  change S (e i) (e j) = _
  have hrel (a b : Fin n) : S (e a) (e b) = 1 ↔ a < b := e.lt_iff_lt
  by_cases hij : i < j
  · simp [transitiveSkew, hij, (hrel i j).mpr hij]
  · by_cases hji : j < i
    · rw [hS.skew, (hrel j i).mpr hji]
      simp [transitiveSkew, hij, hji]
    · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
      subst j
      simp [hS.diag, transitiveSkew]

/-- Precise signed-permutation equivalence: after sign conjugation and one common
row/column permutation, the actual matrix is the transitive tournament matrix. -/
def SignedPermutationTransitive {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∃ e : Equiv.Perm (Fin n),
      (switch S ε).submatrix e e = (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ)

/-- All fourth principal determinants equal to one force signed-permutation
transitivity, for every order including zero, one, two, and three. -/
theorem signedPermutationTransitive_of_allFourDetOne {n : ℕ}
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : IsSkewSign S) (h4 : AllFourDetOne S) :
    SignedPermutationTransitive S := by
  classical
  cases n with
  | zero =>
      refine ⟨fun _ => 1, fun _ => Or.inl rfl, Equiv.refl _, ?_⟩
      ext i; exact Fin.elim0 i
  | succ n =>
      let p : Fin (n + 1) := 0
      let ε := pivotSigns S p
      have hε : ∀ i, ε i = 1 ∨ ε i = -1 := pivotSigns_signs hS p
      have hs : IsSkewSign (switch S ε) := hS.switch ε hε
      obtain ⟨e, he⟩ := exists_relabel_eq_transitive_of_strictTotalOrder
        (Fintype.card_fin (n + 1)) hs (pivot_switch_strictTotalOrder hS h4 p)
      exact ⟨ε, hε, e, he⟩

theorem transitiveSkew_eq_one_iff {n : ℕ} (i j : Fin n) :
    (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) i j = 1 ↔ i < j := by
  by_cases hij : i < j
  · simp [transitiveSkew, hij]
  · by_cases hji : j < i <;> norm_num [transitiveSkew, hij, hji]

theorem transitiveSkew_isSkewSign (n : ℕ) :
    IsSkewSign (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨transitiveSkew_skew n, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · left; exact (transitiveSkew_eq_one_iff i j).mpr h
  · right
    rw [transitiveSkew_skew, (transitiveSkew_eq_one_iff j i).mpr h]

/-- Every four-vertex principal determinant of the transitive sign matrix is one,
independently of the order in which the four vertices are listed. -/
theorem allFourDetOne_transitiveSkew (n : ℕ) :
    AllFourDetOne (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) := by
  intro f hf
  let A := (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).submatrix f f
  have hA : IsSkewSign A := by
    refine ⟨fun i j => transitiveSkew_skew n (f i) (f j), ?_⟩
    intro i j hij
    exact (transitiveSkew_isSkewSign n).signs (f i) (f j) (fun h => hij (hf h))
  have htrans : ∀ i j k, A i j = 1 → A j k = 1 → A i k = 1 := by
    intro i j k hij hjk
    exact (transitiveSkew_eq_one_iff (f i) (f k)).mpr
      (lt_trans ((transitiveSkew_eq_one_iff (f i) (f j)).mp hij)
        ((transitiveSkew_eq_one_iff (f j) (f k)).mp hjk))
  obtain ⟨e, he⟩ := exists_relabel_eq_transitive_of_strictTotalOrder
    (Fintype.card_fin 4) hA (strictTotalOrder_of_transitive hA htrans)
  change A.det = 1
  rw [← Matrix.det_submatrix_equiv_self e A, he]
  rw [det_skew_four _ (transitiveSkew_skew 4)]
  norm_num [transitiveSkew]

/-- The converse uses determinant invariance, rather than asserting that switching
preserves path counts (which is false). -/
theorem allFourDetOne_of_signedPermutationTransitive {n : ℕ}
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : SignedPermutationTransitive S) :
    AllFourDetOne S := by
  classical
  obtain ⟨ε, hε, e, he⟩ := hS
  have hεsq : ∀ i, ε i ^ 2 = 1 := by
    intro i; rcases hε i with h | h <;> rw [h] <;> norm_num
  apply (allFourDetOne_switch_iff S ε hεsq).mp
  intro f hf
  let g : Fin 4 → Fin n := fun i => e.symm (f i)
  have hg : Function.Injective g := e.symm.injective.comp hf
  have hsub : (switch S ε).submatrix f f =
      (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).submatrix g g := by
    rw [← he]
    ext i j
    simp [g, Matrix.submatrix_apply]
  rw [hsub]
  exact allFourDetOne_transitiveSkew n g hg

/-- Full finite four-minor classification for arbitrary real skew sign matrices. -/
theorem allFourDetOne_iff_signedPermutationTransitive {n : ℕ}
    {S : Matrix (Fin n) (Fin n) ℝ} (hS : IsSkewSign S) :
    AllFourDetOne S ↔ SignedPermutationTransitive S :=
  ⟨signedPermutationTransitive_of_allFourDetOne hS,
    allFourDetOne_of_signedPermutationTransitive⟩

/-- The classification instantiated on the genuine tournament sign-matrix definition. -/
theorem tournament_allFourDetOne_iff_signedPermutationTransitive {n : ℕ}
    (T : Tournament n) :
    AllFourDetOne (signMatrix T) ↔ SignedPermutationTransitive (signMatrix T) :=
  allFourDetOne_iff_signedPermutationTransitive (signMatrix_isSkewSign T)

end TournamentHamiltonian.Equality
