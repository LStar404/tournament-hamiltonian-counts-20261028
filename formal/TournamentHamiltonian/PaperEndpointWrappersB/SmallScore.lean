module

public import TournamentHamiltonian.UniformSmallScoreMinor

@[expose] public section

/-! Literal finite-uniform endpoint of manuscript Lemma 4.5. -/
noncomputable section
namespace PaperEndpointWrappersB
open TournamentHamiltonian

/-- A single finite cutoff discharges both internal analytic smallness guards. -/
def smallScoreDelta : ℝ := min (1 / 4) (1 / smallScoreUniformLogConstant)

theorem smallScoreDelta_pos : 0 < smallScoreDelta := by
  unfold smallScoreDelta
  exact lt_min (by norm_num) (one_div_pos.mpr smallScoreUniformLogConstant_pos)

theorem smallScoreDelta_le_quarter : smallScoreDelta ≤ 1 / 4 := min_le_left _ _

theorem logConstant_mul_smallScoreDelta_le_one :
    smallScoreUniformLogConstant * smallScoreDelta ≤ 1 := by
  calc
    _ ≤ smallScoreUniformLogConstant * (1 / smallScoreUniformLogConstant) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) smallScoreUniformLogConstant_pos.le
    _ = 1 := mul_one_div_cancel (ne_of_gt smallScoreUniformLogConstant_pos)

/-- Full finite quantifiers; callers supply no variance or restoration-log hypothesis.
The two deletion sets remain independently chosen. -/
theorem lemma4_5 (B : ℝ) (hB : 0 < B) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∃ N : ℕ, 4 ≤ N ∧
      ∀ n t : ℕ, N ≤ n → ∀ T : Tournament n, ∀ d : ℝ,
        0 ≤ d → (∀ i, |score T i| ≤ d) →
        (t : ℝ) ≤ B * Real.log (n : ℝ) →
        (d + (t : ℝ) + 1) ^ 2 / n ≤ δ →
        ∀ I J : Finset (Fin n), ∀ hI : I.card = t, ∀ hJ : J.card = t,
          |rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J)
              (deletedComplementEquiv I J (hI.trans hJ.symm)) -
            Real.exp (-1) * gaussianFactor T * (((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t))| ≤
              Real.exp (-1) * gaussianFactor T * (((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t)) *
                (C * ((d + (t : ℝ) + 1) ^ 2 / n)) := by
  obtain ⟨N, hN, h⟩ := adjacency_nonprincipal_small_score_uniform hB.le
  refine ⟨smallScoreUniformPermanentConstant, smallScoreDelta,
    smallScoreUniformPermanentConstant_pos, smallScoreDelta_pos, N, by omega, ?_⟩
  intro n t hn T d hd hs hlog hη I J hI hJ
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdSq : d ^ 2 ≤ (d + (t : ℝ) + 1) ^ 2 :=
    (sq_le_sq₀ hd (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) t])
  have hvar : scoreVariance T ≤ 1 := by
    calc
      _ ≤ 4 * d ^ 2 / n := scoreVariance_le_score_budget T hn2 d hd hs
      _ ≤ 4 * ((d + (t : ℝ) + 1) ^ 2 / n) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdSq hn0.le) (by norm_num)
      _ ≤ 4 * smallScoreDelta := mul_le_mul_of_nonneg_left hη (by norm_num)
      _ ≤ 1 := by linarith [smallScoreDelta_le_quarter]
  have hsmall : smallScoreUniformLogConstant * (d + (t : ℝ) + 1) ^ 2 / n ≤ 1 := by
    rw [mul_div_assoc]
    exact (mul_le_mul_of_nonneg_left hη smallScoreUniformLogConstant_pos.le).trans
      logConstant_mul_smallScoreDelta_le_one
  simpa only [mul_div_assoc] using h n t hn T d hd hs hvar hlog hsmall I J hI hJ

/-- The manuscript's actual d = ‖S 1‖∞; `score T` is exactly the row-sum vector.
No score-envelope assumption remains in this specialization. -/
theorem lemma4_5_actual_score (B : ℝ) (hB : 0 < B) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∃ N : ℕ, 4 ≤ N ∧
      ∀ n t : ℕ, N ≤ n → ∀ T : Tournament n,
        (t : ℝ) ≤ B * Real.log (n : ℝ) →
        (‖score T‖ + (t : ℝ) + 1) ^ 2 / n ≤ δ →
        ∀ I J : Finset (Fin n), ∀ hI : I.card = t, ∀ hJ : J.card = t,
          |rectangularPermanent (nonprincipalSubmatrix (adjacency T) I J)
              (deletedComplementEquiv I J (hI.trans hJ.symm)) -
            Real.exp (-1) * gaussianFactor T * (((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t))| ≤
              Real.exp (-1) * gaussianFactor T * (((n - t).factorial : ℝ) / (2 : ℝ) ^ (n - t)) *
                (C * ((‖score T‖ + (t : ℝ) + 1) ^ 2 / n)) := by
  obtain ⟨C, δ, hC, hδ, N, hN, h⟩ := lemma4_5 B hB
  refine ⟨C, δ, hC, hδ, N, hN, ?_⟩
  intro n t hn T hlog hη I J hI hJ
  exact h n t hn T ‖score T‖ (norm_nonneg _) (fun i => by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (score T) i) hlog hη I J hI hJ

end PaperEndpointWrappersB
