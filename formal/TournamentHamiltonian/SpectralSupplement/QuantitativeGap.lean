module

public import TournamentHamiltonian.Equality.SpectralClassification

@[expose] public section

set_option autoImplicit false

namespace TournamentHamiltonian.Equality

/-- Any individual nonnegative odd-moment deficit is bounded by the complete
convergent logarithmic deficit. The coefficient is retained exactly. -/
theorem odd_moment_term_le_log_ratio_product_gap (xs ys : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x < 1)
    (hys : ∀ y ∈ ys, 0 ≤ y ∧ y < 1)
    (hmoments : ∀ k : ℕ, (xs.map (fun x => x ^ (2 * k + 1))).sum ≤
      (ys.map (fun y => y ^ (2 * k + 1))).sum) (k : ℕ) :
    (2 : ℝ) * (1 / (2 * k + 1)) *
      ((ys.map (fun x => x ^ (2 * k + 1))).sum -
       (xs.map (fun x => x ^ (2 * k + 1))).sum) ≤
      Real.log (ys.map ratio).prod - Real.log (xs.map ratio).prod := by
  have hs := (hasSum_log_ratio_product ys hys).sub (hasSum_log_ratio_product xs hxs)
  have hle := hs.summable.le_tsum k (fun j _ =>
    sub_nonneg.mpr (mul_le_mul_of_nonneg_left (hmoments j) (by positivity)))
  rw [hs.tsum_eq] at hle
  simpa only [mul_sub] using hle

theorem actual_spectralRatio_pos {n : ℕ} (T : Tournament n) (hn : 0 < n) :
    0 < spectralRatio T := by
  rw [spectralRatio_eq_paired_product T hn]
  apply ratio_product_pos
  intro x hx
  exact ⟨pairedMasses_nonneg T x hx, (pairedMasses_lt_half T hn x hx).trans (by norm_num)⟩

/-- The literal sixth-moment term of the actual spectral logarithmic series.
All odd-moment comparisons are discharged by the existing finite comparison theorem. -/
theorem sixth_deficit_div_le_log_spectralRatio_gap {n : ℕ}
    (T : Tournament n) (hn : 0 < n) :
    (matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 3) -
      matrixFrobSq (signMatrix T ^ 3)) / (3 * (n : ℝ) ^ 6) ≤
      Real.log (spectralRatio (alternatingTournament n) / spectralRatio T) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := odd_moment_term_le_log_ratio_product_gap
    (pairedMasses T) (pairedMasses (alternatingTournament n))
    (fun x hx => ⟨pairedMasses_nonneg T x hx,
      (pairedMasses_lt_half T hn x hx).trans (by norm_num)⟩)
    (fun x hx => ⟨pairedMasses_nonneg _ x hx,
      (pairedMasses_lt_half _ hn x hx).trans (by norm_num)⟩)
    (pairedMasses_odd_pow_sum_le_alternating T hn) 1
  norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_one] at hs
  rw [pairedMasses_pow_sum_eq_frob T hn 3 (by omega),
    pairedMasses_pow_sum_eq_frob (alternatingTournament n) hn 3 (by omega),
    matrixFrobSq_alternating_pow, signMatrix_transitiveTournament] at hs
  rw [Real.log_div (actual_spectralRatio_pos _ hn).ne' (actual_spectralRatio_pos T hn).ne',
    spectralRatio_eq_paired_product T hn,
    spectralRatio_eq_paired_product (alternatingTournament n) hn]
  convert hs using 1
  field_simp

/-- The actual non-signed-transitive class has the manuscript's explicit logarithmic gap. -/
theorem log_spectralRatio_gap_ge_of_not_signedPermutationTransitive {n : ℕ}
    (T : Tournament n) (hT : ¬ SignedPermutationTransitive (signMatrix T)) :
    16 / (3 * (n : ℝ) ^ 6) ≤
      Real.log (spectralRatio (alternatingTournament n) / spectralRatio T) := by
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < 2)
    (two_le_of_not_signedPermutationTransitive T hT)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_div_of_nonneg_right
    (sixth_moment_gap_sixteen_of_not_signedPermutationTransitive T hT) (by positivity)).trans
    (sixth_deficit_div_le_log_spectralRatio_gap T hn)

/-- Exponentiating yields an explicit relative loss in the actual spectral ratio. -/
theorem spectralRatio_le_exp_gap_of_not_signedPermutationTransitive {n : ℕ}
    (T : Tournament n) (hT : ¬ SignedPermutationTransitive (signMatrix T)) :
    spectralRatio T ≤ spectralRatio (alternatingTournament n) *
      Real.exp (-(16 / (3 * (n : ℝ) ^ 6))) := by
  have hn : 0 < n := by have := two_le_of_not_signedPermutationTransitive T hT; omega
  have hpT := actual_spectralRatio_pos T hn
  have hpU := actual_spectralRatio_pos (alternatingTournament n) hn
  have hlog := log_spectralRatio_gap_ge_of_not_signedPermutationTransitive T hT
  rw [Real.log_div hpU.ne' hpT.ne'] at hlog
  have he := Real.exp_le_exp.mpr (show Real.log (spectralRatio T) ≤
      Real.log (spectralRatio (alternatingTournament n)) - 16 / (3 * (n : ℝ) ^ 6) by linarith)
  simpa only [Real.exp_sub, Real.exp_log hpT, Real.exp_log hpU, Real.exp_neg, div_eq_mul_inv] using he

/-- The explicit additive loss is positive; this is not merely an unspecified strict bound. -/
theorem spectralRatio_sub_ge_exp_gap_of_not_signedPermutationTransitive {n : ℕ}
    (T : Tournament n) (hT : ¬ SignedPermutationTransitive (signMatrix T)) :
    spectralRatio (alternatingTournament n) * (1 - Real.exp (-(16 / (3 * (n : ℝ) ^ 6)))) ≤
      spectralRatio (alternatingTournament n) - spectralRatio T ∧
    0 < spectralRatio (alternatingTournament n) * (1 - Real.exp (-(16 / (3 * (n : ℝ) ^ 6)))) := by
  have hn : 0 < n := by have := two_le_of_not_signedPermutationTransitive T hT; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · have := spectralRatio_le_exp_gap_of_not_signedPermutationTransitive T hT
    nlinarith
  · apply mul_pos (actual_spectralRatio_pos _ hn)
    have he : Real.exp (-(16 / (3 * (n : ℝ) ^ 6))) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact neg_neg_of_pos (by positivity)
    linarith

/-- The regular non-carousel instance uses ordinary isomorphism, not switching. -/
theorem regular_noncarousel_quantitative_spectral_gap (m : ℕ)
    (T : Tournament (2 * m + 1)) (hreg : ∀ i, score T i = 0)
    (hnot : ¬ ∃ e : Equiv.Perm (Fin (2 * m + 1)),
      relabelTournament T e = carouselTournament m) :
    16 / (3 * ((2 * m + 1 : ℕ) : ℝ) ^ 6) ≤
      Real.log (spectralRatio (carouselTournament m) / spectralRatio T) ∧
    spectralRatio T ≤ spectralRatio (carouselTournament m) *
      Real.exp (-(16 / (3 * ((2 * m + 1 : ℕ) : ℝ) ^ 6))) ∧
    spectralRatio (carouselTournament m) *
      (1 - Real.exp (-(16 / (3 * ((2 * m + 1 : ℕ) : ℝ) ^ 6)))) ≤
      spectralRatio (carouselTournament m) - spectralRatio T ∧
    0 < spectralRatio (carouselTournament m) *
      (1 - Real.exp (-(16 / (3 * ((2 * m + 1 : ℕ) : ℝ) ^ 6)))) := by
  have hT : ¬ SignedPermutationTransitive (signMatrix T) := by
    intro h
    exact hnot ((tournament_regular_signedPermutationTransitive_iff_relabel_carousel m T hreg).mp h)
  rw [carousel_spectralRatio_eq_alternating]
  exact ⟨log_spectralRatio_gap_ge_of_not_signedPermutationTransitive T hT,
    spectralRatio_le_exp_gap_of_not_signedPermutationTransitive T hT,
    spectralRatio_sub_ge_exp_gap_of_not_signedPermutationTransitive T hT⟩

end TournamentHamiltonian.Equality
