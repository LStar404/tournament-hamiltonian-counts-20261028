module

public import TournamentHamiltonian.UniformBlowup.Normalization
public import TournamentHamiltonian.UniformBlowup.BlockDistribution
public import TournamentHamiltonian.RegularOrientation.Blowup
public import TournamentHamiltonian.HighVariance

@[expose] public section

set_option autoImplicit false

namespace NonregularDecay
open TournamentHamiltonian UniformBlowup
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The genuine sign matrix, transported across the specified vertex labelling. -/
theorem sign_blowup {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) (u v : Vertex d m) :
    signMatrix (blowup T ω e) (e.symm u) (e.symm v) =
      if u.1 = v.1 then
        signMatrix (blockTournamentEquiv d m ω u.1) u.2 v.2
      else signMatrix T u.1 v.1 := by
  rcases u with ⟨i,a⟩
  rcases v with ⟨j,b⟩
  by_cases hij : i = j
  · subst j
    simp [signMatrix, blowup, arc, blockTournamentEquiv, tournamentEquiv,
      internalTournament]
    rfl
  · have huv : (i,a) ≠ (j,b) := fun h => hij (congrArg Prod.fst h)
    simp [signMatrix, blowup, arc, hij, huv]

/-- Every vertex has its base score multiplied by the block size, plus its
actual internal-tournament score. No regularity or randomness is assumed. -/
theorem score_blowup {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) (u : Vertex d m) :
    score (blowup T ω e) (e.symm u) =
      (m : ℝ) * score T u.1 + score (blockTournamentEquiv d m ω u.1) u.2 := by
  unfold score
  rw [← e.symm.sum_comp]
  simp_rw [sign_blowup]
  rw [Fintype.sum_prod_type]
  have hrow (i : Fin d) :
      (∑ a : Fin m, if u.1 = i then
          signMatrix (blockTournamentEquiv d m ω u.1) u.2 a
        else signMatrix T u.1 i) =
        (m : ℝ) * signMatrix T u.1 i +
          if u.1 = i then score (blockTournamentEquiv d m ω u.1) u.2 else 0 := by
    by_cases hi : u.1 = i
    · subst i
      simp [signMatrix, score]
    · simp [hi]
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [score]

/-- Exact score-square decomposition. Internal zero-sum scores eliminate all
cross terms, for every assignment of internal tournaments. -/
theorem score_square_sum_blowup {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) :
    (∑ v, score (blowup T ω e) v ^ 2) =
      (m : ℝ)^3 * (∑ i, score T i ^ 2) +
        ∑ i, ∑ a, score (blockTournamentEquiv d m ω i) a ^ 2 := by
  rw [← e.symm.sum_comp]
  simp_rw [score_blowup]
  rw [Fintype.sum_prod_type]
  have hrow (i : Fin d) :
      (∑ a : Fin m, ((m : ℝ) * score T i +
          score (blockTournamentEquiv d m ω i) a)^2) =
        (m : ℝ)^3 * score T i^2 +
          ∑ a, score (blockTournamentEquiv d m ω i) a^2 := by
    simp_rw [add_sq, mul_pow]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, score_sum_zero, mul_zero, add_zero]
    ring
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Blowup degree variance is exactly cubic base variance plus internal variance. -/
theorem degreeVariance_blowup {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) :
    degreeVariance (blowup T ω e) =
      (m : ℝ)^3 * degreeVariance T + ∑ i, degreeVariance (blockTournamentEquiv d m ω i) := by
  simp_rw [degreeVariance_eq_score_sum]
  rw [score_square_sum_blowup]
  rw [← Finset.sum_div]
  ring

theorem degreeVariance_nonneg {n : ℕ} (T : Tournament n) : 0 ≤ degreeVariance T := by
  rw [degreeVariance_eq_score_sum]
  positivity

/-- The lower bound is uniform over all internal blocks and all labellings. -/
theorem degreeVariance_blowup_ge {d m : ℕ} (T : Tournament d) (ω : Sample d m)
    (e : Arrangement d m) :
    (m : ℝ)^3 * degreeVariance T ≤ degreeVariance (blowup T ω e) := by
  rw [degreeVariance_blowup]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => degreeVariance_nonneg _)

theorem degreeVariance_pos_iff_nonregular {d : ℕ} (T : Tournament d) :
    0 < degreeVariance T ↔ ¬RegularOrientation.IsRegular T := by
  rw [degreeVariance_eq_score_sum]
  have hn : 0 ≤ ∑ i, score T i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  constructor
  · intro hp hr
    have hz : (∑ i, score T i ^ 2) = 0 := by
      have hr' : ∀ i, score T i = 0 := hr
      simp [hr']
    rw [hz] at hp
    norm_num at hp
  · intro h
    have hex : ∃ i, score T i ≠ 0 := by simpa [RegularOrientation.IsRegular] using h
    obtain ⟨i, hi⟩ := hex
    have hs : 0 < score T i ^ 2 := sq_pos_of_ne_zero hi
    have hle : score T i^2 ≤ ∑ j, score T j^2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    exact div_pos (hs.trans_le hle) (by norm_num)

end
end NonregularDecay
