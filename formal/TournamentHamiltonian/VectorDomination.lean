module

public import TournamentHamiltonian.FiniteComparisonOrder
public import TournamentHamiltonian.SignedIndicatorBound

/-!
# From signed indicator counts to all-power column domination

Finite Abel summation is the signed-layer argument in compressed form:
the signed indicator estimate bounds all prefixes of a coefficient vector,
which is then weighted by the decreasing absolute input coordinates.
No matrix comparison is assumed in the final power theorem.
-/

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open scoped BigOperators Matrix

noncomputable def coordinateSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

theorem coordinateSign_cases (x : ℝ) : coordinateSign x = 1 ∨ coordinateSign x = -1 := by
  unfold coordinateSign
  split_ifs <;> simp

theorem coordinateSign_mul_abs (x : ℝ) : coordinateSign x * |x| = x := by
  unfold coordinateSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem coordinateSign_mul_self (x : ℝ) : coordinateSign x * x = |x| := by
  unfold coordinateSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

def signedSelectionCoeff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (S : Finset (Fin n)) (ε η : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (j : Fin n) : ℝ :=
  ∑ i ∈ S, ε i * A i (π j) * η (π j)

theorem signedSelectionCoeff_prefix_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) (hentry : ∀ i j, |A i j| ≤ 1)
    (S : Finset (Fin n)) (ε η : Fin n → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hη : ∀ i, η i = 1 ∨ η i = -1)
    (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    finPrefixSum (signedSelectionCoeff A S ε η π) k ≤ blockBudget n S.card k := by
  classical
  have h := signed_indicator_bilinear_le A hskew hentry S ((finPrefix n k).image π) ε η hε hη
  rw [Finset.card_image_of_injective _ π.injective, finPrefix_card n k hk] at h
  simp_rw [Finset.sum_image π.injective.injOn] at h
  rw [Finset.sum_comm] at h
  exact h

theorem selected_abs_mulVec_eq_sorted_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (S : Finset (Fin n)) (π : Equiv.Perm (Fin n)) :
    (∑ i ∈ S, |(A *ᵥ x) i|) =
      ∑ j, signedSelectionCoeff A S (fun i => coordinateSign ((A *ᵥ x) i))
        (fun j => coordinateSign (x j)) π j * |x (π j)| := by
  symm
  calc
    _ = ∑ j, ∑ i ∈ S, coordinateSign ((A *ᵥ x) i) * A i (π j) * x (π j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [signedSelectionCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_assoc, coordinateSign_mul_abs]
    _ = ∑ j, ∑ i ∈ S, coordinateSign ((A *ᵥ x) i) * A i j * x j := by
      apply Fintype.sum_equiv π
      intro j
      rfl
    _ = ∑ i ∈ S, ∑ j, coordinateSign ((A *ᵥ x) i) * A i j * x j := Finset.sum_comm
    _ = ∑ i ∈ S, coordinateSign ((A *ᵥ x) i) * (A *ᵥ x) i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact coordinateSign_mul_self _

theorem absDom_mulVec_comparison_sorted {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) (hentry : ∀ i j, |A i j| ≤ 1)
    (x : Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (ha : DecreasingNonneg (fun i => |x (π i)|)) :
    AbsDom (A *ᵥ x) (comparisonMatrix n *ᵥ (fun i => |x (π i)|)) := by
  classical
  intro S
  let ε : Fin n → ℝ := fun i => coordinateSign ((A *ᵥ x) i)
  let η : Fin n → ℝ := fun j => coordinateSign (x j)
  let c := signedSelectionCoeff A S ε η π
  let w : Fin n → ℝ := fun j => (comparisonPrefix n S.card j.val : ℝ)
  have hr : S.card ≤ n := by simpa using S.card_le_univ
  have hp : ∀ k ≤ n, finPrefixSum c k ≤ finPrefixSum w k := by
    intro k hk
    have h := signedSelectionCoeff_prefix_le A hskew hentry S ε η
      (fun i => coordinateSign_cases _) (fun j => coordinateSign_cases _) π k hk
    simpa only [c, w, finComparison_prefix_weight_sum S.card k hr hk] using h
  have hdot := finite_dot_le_of_prefix_le c w (fun i => |x (π i)|) ha.1 ha.2 hp
  rw [selected_abs_mulVec_eq_sorted_dot A x S π]
  apply hdot.trans_eq
  rw [finComparison_prefix_mulVec _ S.card hr]

/-- One-step absolute-subset domination. The indicator bound discharges the
matrix comparison; no such comparison is a caller-supplied premise. -/
theorem absDom_mulVec_comparison {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) (hentry : ∀ i j, |A i j| ≤ 1)
    {x y : Fin n → ℝ} (hxy : AbsDom x y) :
    AbsDom (A *ᵥ x) (comparisonMatrix n *ᵥ y) := by
  obtain ⟨π, ha⟩ := sorted_abs_exists x
  have hsingle := absDom_mulVec_comparison_sorted A hskew hentry x π ha
  have hp := comparisonMatrix_preserves_finPrefix (fun i => |x (π i)|) y
    (fun r hr => absDom_sorted_prefix hxy π r hr)
  intro S
  exact (hsingle S).trans (hp S.card (by simpa using S.card_le_univ))

def finiteBasisVector {n : ℕ} (j : Fin n) : Fin n → ℝ :=
  fun i => if i = j then 1 else 0

theorem absDom_basis {n : ℕ} (hn : 0 < n) (j : Fin n) :
    AbsDom (finiteBasisVector j) (finiteBasisVector ⟨0, hn⟩) := by
  classical
  intro S
  by_cases hs : S = ∅
  · simp [hs, finPrefixSum]
  · have hc : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
    have hz : (⟨0, hn⟩ : Fin n) ∈ finPrefix n S.card := by simpa using hc
    have hab : ∀ i : Fin n, |if i = j then (1 : ℝ) else 0| =
        if i = j then 1 else 0 := by
      intro i
      split_ifs <;> norm_num
    by_cases hj : j ∈ S <;> simp [finiteBasisVector, finPrefixSum, hab, hj, hz]

theorem skew_pow_basis_absDom {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hskew : ∀ i j, A i j = -A j i) (hentry : ∀ i j, |A i j| ≤ 1)
    (p : ℕ) (j : Fin n) :
    AbsDom ((A ^ p) *ᵥ finiteBasisVector j)
      (((comparisonMatrix n) ^ p) *ᵥ finiteBasisVector ⟨0, hn⟩) := by
  induction p with
  | zero => simpa using absDom_basis hn j
  | succ p ih =>
    simpa only [pow_succ', Matrix.mulVec_mulVec] using absDom_mulVec_comparison A hskew hentry ih

/-- Every real skew, entrywise-bounded matrix is dominated columnwise at
every power by the first column of K at the same power. -/
theorem skew_pow_column_sq_le_comparison {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hn : 0 < n) (hskew : A.transpose = -A) (hentry : ∀ i j, |A i j| ≤ 1)
    (p : ℕ) (j : Fin n) :
    (∑ i, ((A ^ p) i j) ^ 2) ≤ ∑ i, (((comparisonMatrix n) ^ p) i ⟨0, hn⟩) ^ 2 := by
  have hpoint : ∀ i j, A i j = -A j i := by
    intro i j
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using congrFun (congrFun hskew j) i
  have h := sum_sq_le_of_absDom (skew_pow_basis_absDom A hn hpoint hentry p j)
  simpa only [Matrix.mulVec, dotProduct, finiteBasisVector, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

end TournamentHamiltonian
