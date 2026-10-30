module

public import TournamentHamiltonian.Equality.FourthMomentAlgebra
public import TournamentHamiltonian.Equality.SignedPermutationClassification

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

open scoped BigOperators Matrix

/-- A repeated vertex makes the actual principal submatrix singular. -/
theorem det_four_submatrix_eq_zero_of_not_injective {ι : Type*}
    (A : Matrix ι ι ℝ) (f : Fin 4 → ι) (hf : ¬ Function.Injective f) :
    (A.submatrix f f).det = 0 := by
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hf
  exact Matrix.det_zero_of_row_eq hne (by funext k; exact congrArg (fun x => A x (f k)) hij)

/-- Arbitrary real skew-sign matrices, not only Boolean tournament wrappers. -/
theorem IsSkewSign.det_four_eq_one_or_nine {ι : Type*} {A : Matrix ι ι ℝ}
    (hA : IsSkewSign A) (f : Fin 4 → ι) (hf : Function.Injective f) :
    (A.submatrix f f).det = 1 ∨ (A.submatrix f f).det = 9 := by
  rw [det_skew_four (A.submatrix f f) (fun i j => hA.skew (f i) (f j))]
  have hsigns (i j : Fin 4) (hij : i ≠ j) :=
    hA.signs (f i) (f j) (fun h => hij (hf h))
  simpa only [det_skewFour, Matrix.submatrix_apply] using
    det_skewFour_eq_one_or_nine (A (f 0) (f 1)) (A (f 0) (f 2)) (A (f 0) (f 3))
      (A (f 1) (f 2)) (A (f 1) (f 3)) (A (f 2) (f 3))
      (hsigns 0 1 (by decide)) (hsigns 0 2 (by decide)) (hsigns 0 3 (by decide))
      (hsigns 1 2 (by decide)) (hsigns 1 3 (by decide)) (hsigns 2 3 (by decide))

theorem matrixFrobSq_eq_of_isSkewSign {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSkewSign A) (hB : IsSkewSign B) : matrixFrobSq A = matrixFrobSq B := by
  unfold matrixFrobSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  by_cases hij : i = j
  · subst j; rw [hA.diag i, hB.diag i]
  · rcases hA.signs i j hij with ha | ha <;>
      rcases hB.signs i j hij with hb | hb <;> rw [ha,hb] <;> norm_num

/-- A genuine pointwise principal-minor inequality, including repeated indices. -/
theorem transitive_four_det_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSkewSign A) (f : Fin 4 → Fin n) :
    ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).submatrix f f).det ≤
      (A.submatrix f f).det := by
  by_cases hf : Function.Injective f
  · rw [allFourDetOne_transitiveSkew n f hf]
    rcases hA.det_four_eq_one_or_nine f hf with h | h <;> rw [h] <;> norm_num
  · rw [det_four_submatrix_eq_zero_of_not_injective _ f hf,
      det_four_submatrix_eq_zero_of_not_injective _ f hf]

/-- Equality in a fourfold finite sum of termwise bounds is termwise equality. -/
theorem sumFour_eq_iff_of_le {n : ℕ}
    (f g : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h : ∀ i j k l, f i j k l ≤ g i j k l) :
    sumFour f = sumFour g ↔ ∀ i j k l, f i j k l = g i j k l := by
  constructor
  · intro heq i j k l
    have h1 := (Finset.sum_eq_sum_iff_of_le (fun a _ =>
      Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun c _ =>
        Finset.sum_le_sum (fun d _ => h a b c d))))).mp heq i (Finset.mem_univ i)
    have h2 := (Finset.sum_eq_sum_iff_of_le (fun b _ =>
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun d _ => h i b c d)))).mp
        h1 j (Finset.mem_univ j)
    have h3 := (Finset.sum_eq_sum_iff_of_le (fun c _ =>
      Finset.sum_le_sum (fun d _ => h i j c d))).mp h2 k (Finset.mem_univ k)
    exact (Finset.sum_eq_sum_iff_of_le (fun d _ => h i j k d)).mp h3 l (Finset.mem_univ l)
  · exact sumFour_congr

/-- Equality of the actual four-minor sums is exactly the actual all-four criterion. -/
theorem fourDetTotal_eq_transitive_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSkewSign A) :
    fourDetTotal A = fourDetTotal (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ↔
      AllFourDetOne A := by
  constructor
  · intro heq f hf
    have hterms := (sumFour_eq_iff_of_le
      (fun i j k l => ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ).submatrix
        ![i,j,k,l] ![i,j,k,l]).det)
      (fun i j k l => (A.submatrix ![i,j,k,l] ![i,j,k,l]).det)
      (fun i j k l => transitive_four_det_le hA ![i,j,k,l])).mp heq.symm
    have hvec : ![f 0, f 1, f 2, f 3] = f := by funext i; fin_cases i <;> rfl
    have ht := hterms (f 0) (f 1) (f 2) (f 3)
    rw [hvec, allFourDetOne_transitiveSkew n f hf] at ht
    exact ht.symm
  · intro h4
    apply sumFour_congr
    intro i j k l
    let f : Fin 4 → Fin n := ![i,j,k,l]
    by_cases hf : Function.Injective f
    · exact (h4 f hf).trans (allFourDetOne_transitiveSkew n f hf).symm
    · exact (det_four_submatrix_eq_zero_of_not_injective A f hf).trans
        (det_four_submatrix_eq_zero_of_not_injective _ f hf).symm

/-- The fourth-moment equality criterion. No size lower bound is needed. -/
theorem frob_sq_eq_transitive_iff_allFourDetOne {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSkewSign A) :
    matrixFrobSq (A ^ 2) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 2) ↔
      AllFourDetOne A := by
  have h0 := matrixFrobSq_eq_of_isSkewSign hA (transitiveSkew_isSkewSign n)
  have hA4 := fourDetTotal_eq A hA.skew
  have hT4 := fourDetTotal_eq (transitiveSkew n : Matrix (Fin n) (Fin n) ℝ)
    (transitiveSkew_isSkewSign n).skew
  rw [h0] at hA4
  rw [← fourDetTotal_eq_transitive_iff hA]
  constructor <;> intro h <;> linarith

/-- Exact interface to the high-power and paired-mass equality descent. -/
theorem tournament_frob_sq_eq_transitive_iff_allFourDetOne {n : ℕ} (T : Tournament n) :
    matrixFrobSq ((signMatrix T) ^ 2) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 2) ↔
      AllFourDetOne (signMatrix T) :=
  frob_sq_eq_transitive_iff_allFourDetOne (signMatrix_isSkewSign T)

end TournamentHamiltonian.Equality
