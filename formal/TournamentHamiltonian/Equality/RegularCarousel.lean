module

public import TournamentHamiltonian.Equality.SignedPermutationMatrix
public import TournamentHamiltonian.Carousel

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

/-- Consecutive rows of the transitive sign matrix differ at exactly two entries. -/
theorem transitiveSkew_consecutive_rows (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    (transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.castSucc j -
      transitiveSkew (n + 1) i.succ j =
      (if j = i.castSucc then 1 else 0) + (if j = i.succ then 1 else 0) := by
  simp only [transitiveSkew, Fin.lt_def, Fin.val_castSucc, Fin.val_succ,
    Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> norm_num at * <;> omega

/-- Every vector in the transitive kernel has alternating consecutive entries. -/
theorem transitive_kernel_consecutive (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, ∑ j, (transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j * v j = 0)
    (i : Fin n) : v i.succ = -v i.castSucc := by
  have hsum : v i.castSucc + v i.succ = 0 := by
    calc
      _ = ∑ j : Fin (n + 1),
          ((if j = i.castSucc then (1 : ℝ) else 0) + (if j = i.succ then 1 else 0)) * v j := by
        simp [add_mul, Finset.sum_add_distrib]
      _ = ∑ j, ((transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i.castSucc j -
          transitiveSkew (n + 1) i.succ j) * v j := by
        simp only [transitiveSkew_consecutive_rows]
      _ = 0 := by simp only [sub_mul, Finset.sum_sub_distrib, hv, sub_self]
  linarith

/-- The transitive kernel is contained in the one-dimensional alternating line.
At even positive orders this forces the vector to vanish, but that strengthening
is not needed for the regular-tournament classification. -/
theorem transitive_kernel_alternating (n : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, ∑ j, (transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j * v j = 0) :
    ∀ i : Fin (n + 1), v i = alternatingSign i.val * v 0 := by
  intro i
  induction i using Fin.induction with
  | zero => simp [alternatingSign]
  | succ i ih =>
    rw [transitive_kernel_consecutive n v hv i, ih]
    simp [alternatingSign, pow_succ]

/-- A regular matrix signed-permutation equivalent to the transitive matrix is
ordinary-permutation equivalent to the alternating construction. -/
theorem regular_signedPermutationTransitive_relabel_alternating {n : ℕ}
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hreg : ∀ i, ∑ j, S i j = 0) (hclass : SignedPermutationTransitive S) :
    ∃ e : Equiv.Perm (Fin (n + 1)), S.submatrix e e = alternatingSkew (n + 1) := by
  classical
  obtain ⟨ε, hε, e, he⟩ := hclass
  let η : Fin (n + 1) → ℝ := ε ∘ e
  have hηsq (i : Fin (n + 1)) : η i ^ 2 = 1 := by
    rcases hε (e i) with h | h <;> simp [η, h]
  have hentry (i j : Fin (n + 1)) :
      η i * S (e i) (e j) * η j =
        (transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j :=
    congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => A i j) he
  have hkernel (i : Fin (n + 1)) :
      ∑ j, (transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j * η j = 0 := by
    calc
      _ = ∑ j, η i * S (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← hentry]
        calc
          _ = (η i * S (e i) (e j)) * (η j ^ 2) := by ring
          _ = _ := by rw [hηsq, mul_one]
      _ = η i * ∑ j, S (e i) (e j) := by rw [Finset.mul_sum]
      _ = η i * ∑ j, S (e i) j := by rw [Equiv.sum_comp e]
      _ = 0 := by rw [hreg, mul_zero]
  have halt := transitive_kernel_alternating n η hkernel
  refine ⟨e, ?_⟩
  ext i j
  change S (e i) (e j) = _
  calc
    _ = η i * (η i * S (e i) (e j) * η j) * η j := by
      calc
        _ = (η i ^ 2) * S (e i) (e j) * (η j ^ 2) := by rw [hηsq, hηsq]; ring
        _ = _ := by ring
    _ = η i * transitiveSkew (n + 1) i j * η j := by rw [hentry]
    _ = alternatingSkew (n + 1) i j := by
      rw [halt i, halt j]
      dsimp [alternatingSkew]
      calc
        _ = (alternatingSign i.val * alternatingSign j.val *
          (transitiveSkew (n + 1) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) i j) * (η 0 ^ 2) := by ring
        _ = _ := by rw [hηsq, mul_one]

/-- Simultaneous row/column relabelling preserves the four-principal-minor criterion. -/
theorem allFourDetOne_submatrix_equiv_iff {ι κ : Type*}
    (S : Matrix ι ι ℝ) (e : κ ≃ ι) :
    AllFourDetOne (S.submatrix e e) ↔ AllFourDetOne S := by
  constructor
  · intro h f hf
    have h' := h (e.symm ∘ f) (e.symm.injective.comp hf)
    simpa [Matrix.submatrix_submatrix, Function.comp_def] using h'
  · intro h f hf
    have h' := h (e ∘ f) (e.injective.comp hf)
    simpa [Matrix.submatrix_submatrix, Function.comp_def] using h'

/-- Genuine tournament orientations are determined by their actual sign matrices. -/
theorem tournament_eq_of_signMatrix_eq {n : ℕ} (T U : Tournament n)
    (h : signMatrix T = signMatrix U) : T = U := by
  apply Subtype.ext
  funext i j
  by_cases hij : i = j
  · subst j
    simp [T.property.1, U.property.1]
  · have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) h
    cases ht : T.val i j <;> cases hu : U.val i j <;> try rfl
    all_goals norm_num [signMatrix, hij, ht, hu] at hentry

/-- The existing alternating construction has exactly the good fourth minors. -/
theorem allFourDetOne_alternatingTournament (n : ℕ) :
    AllFourDetOne (signMatrix (alternatingTournament n)) := by
  have heq : signMatrix (alternatingTournament n) =
      switch (transitiveSkew n) (fun i : Fin n => (alternatingSign i.val : ℝ)) := by
    rw [signMatrix_alternatingTournament]
    ext i j
    dsimp [alternatingSkew, switch]
    ring
  rw [heq]
  exact (allFourDetOne_switch_iff (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ)
    (fun i : Fin n => (alternatingSign i.val : ℝ))
    (fun i => alternatingSign_sq (K := ℝ) i.val)).mpr
    (allFourDetOne_transitiveSkew n)

theorem allFourDetOne_carouselTournament (m : ℕ) :
    AllFourDetOne (signMatrix (carouselTournament m)) := by
  rw [carouselTournament_eq_relabel, signMatrix_relabelTournament]
  exact (allFourDetOne_submatrix_equiv_iff _ _).mpr
    (allFourDetOne_alternatingTournament (2 * m + 1))

/-- The ordinary-isomorphism conclusion: regularity removes the extra switching
freedom. The witness is only a vertex permutation, with no sign changes. -/
theorem tournament_regular_allFourDetOne_iff_relabel_carousel (m : ℕ)
    (T : Tournament (2 * m + 1)) (hreg : ∀ i, score T i = 0) :
    AllFourDetOne (signMatrix T) ↔
      ∃ e : Equiv.Perm (Fin (2 * m + 1)), relabelTournament T e = carouselTournament m := by
  constructor
  · intro h4
    have hclass := (tournament_allFourDetOne_iff_signedPermutationTransitive T).mp h4
    obtain ⟨e, he⟩ := regular_signedPermutationTransitive_relabel_alternating hreg hclass
    have halt : relabelTournament T e = alternatingTournament (2 * m + 1) := by
      apply tournament_eq_of_signMatrix_eq
      rw [signMatrix_relabelTournament, signMatrix_alternatingTournament]
      exact he
    refine ⟨(carouselOrder m).trans e, ?_⟩
    calc
      _ = relabelTournament (relabelTournament T e) (carouselOrder m) := rfl
      _ = relabelTournament (alternatingTournament (2 * m + 1)) (carouselOrder m) := by rw [halt]
      _ = carouselTournament m := (carouselTournament_eq_relabel m).symm
  · rintro ⟨e, he⟩
    have h4 := allFourDetOne_carouselTournament m
    rw [← he, signMatrix_relabelTournament] at h4
    exact (allFourDetOne_submatrix_equiv_iff _ _).mp h4

/-- Equivalent ordinary-carousel endpoint stated directly with the signed-permutation
class; the actual regularity hypothesis remains explicit. -/
theorem tournament_regular_signedPermutationTransitive_iff_relabel_carousel (m : ℕ)
    (T : Tournament (2 * m + 1)) (hreg : ∀ i, score T i = 0) :
    SignedPermutationTransitive (signMatrix T) ↔
      ∃ e : Equiv.Perm (Fin (2 * m + 1)), relabelTournament T e = carouselTournament m := by
  rw [← tournament_allFourDetOne_iff_signedPermutationTransitive T]
  exact tournament_regular_allFourDetOne_iff_relabel_carousel m T hreg

end TournamentHamiltonian.Equality
