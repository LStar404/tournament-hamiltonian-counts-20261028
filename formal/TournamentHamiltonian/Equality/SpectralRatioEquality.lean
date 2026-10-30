module

public import TournamentHamiltonian.Equality.SpectralEqualityDescent
public import TournamentHamiltonian.SharpSpectralMoments

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

/-- One strict odd moment, with all the others weakly bounded, makes the
positive-coefficient log-series comparison strict. -/
theorem ratio_product_lt_of_odd_moments (xs ys : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x < 1)
    (hys : ∀ y ∈ ys, 0 ≤ y ∧ y < 1)
    (hmoments : ∀ k : ℕ, (xs.map (fun x => x ^ (2 * k + 1))).sum ≤
      (ys.map (fun y => y ^ (2 * k + 1))).sum)
    (k : ℕ) (hstrict : (xs.map (fun x => x ^ (2 * k + 1))).sum <
      (ys.map (fun y => y ^ (2 * k + 1))).sum) :
    (xs.map ratio).prod < (ys.map ratio).prod := by
  have hxpos := ratio_product_pos xs hxs
  have hypos := ratio_product_pos ys hys
  apply (Real.log_lt_log_iff hxpos hypos).mp
  exact hasSum_lt
    (fun j => mul_le_mul_of_nonneg_left (hmoments j) (by positivity))
    (mul_lt_mul_of_pos_left hstrict (by positivity))
    (hasSum_log_ratio_product xs hxs) (hasSum_log_ratio_product ys hys)

/-- Equal products under all odd-moment bounds force equality of each odd
moment; finite-list convergence is proved by the imported HasSum endpoint. -/
theorem odd_moments_eq_of_ratio_product_eq (xs ys : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x < 1)
    (hys : ∀ y ∈ ys, 0 ≤ y ∧ y < 1)
    (hmoments : ∀ k : ℕ, (xs.map (fun x => x ^ (2 * k + 1))).sum ≤
      (ys.map (fun y => y ^ (2 * k + 1))).sum)
    (heq : (xs.map ratio).prod = (ys.map ratio).prod) (k : ℕ) :
    (xs.map (fun x => x ^ (2 * k + 1))).sum =
      (ys.map (fun y => y ^ (2 * k + 1))).sum := by
  rcases lt_or_eq_of_le (hmoments k) with hlt | hsame
  · exact False.elim ((ne_of_lt (ratio_product_lt_of_odd_moments xs ys hxs hys hmoments k hlt)) heq)
  · exact hsame

/-- Strict odd-moment comparison for two actual tournament spectra. -/
theorem spectralRatio_lt_of_odd_paired_moments {n : ℕ} (T U : Tournament n) (hn : 0 < n)
    (hmoments : ∀ k : ℕ, ((pairedMasses T).map (fun x => x ^ (2 * k + 1))).sum ≤
      ((pairedMasses U).map (fun x => x ^ (2 * k + 1))).sum)
    (k : ℕ) (hstrict : ((pairedMasses T).map (fun x => x ^ (2 * k + 1))).sum <
      ((pairedMasses U).map (fun x => x ^ (2 * k + 1))).sum) :
    spectralRatio T < spectralRatio U := by
  rw [spectralRatio_eq_paired_product T hn, spectralRatio_eq_paired_product U hn]
  apply ratio_product_lt_of_odd_moments _ _ _ _ hmoments k hstrict
  · intro x hx
    exact ⟨pairedMasses_nonneg T x hx, (pairedMasses_lt_half T hn x hx).trans (by norm_num)⟩
  · intro x hx
    exact ⟨pairedMasses_nonneg U x hx, (pairedMasses_lt_half U hn x hx).trans (by norm_num)⟩

/-- Equality with the alternating/transitive ratio forces all odd paired
moments to saturate, using the unconditional finite matrix comparison. -/
theorem pairedMasses_odd_pow_eq_of_spectralRatio_eq {n : ℕ} (T : Tournament n) (hn : 0 < n)
    (heq : spectralRatio T = spectralRatio (alternatingTournament n)) (k : ℕ) :
    ((pairedMasses T).map (fun x => x ^ (2 * k + 1))).sum =
      ((pairedMasses (alternatingTournament n)).map (fun x => x ^ (2 * k + 1))).sum := by
  rw [spectralRatio_eq_paired_product T hn,
    spectralRatio_eq_paired_product (alternatingTournament n) hn] at heq
  apply odd_moments_eq_of_ratio_product_eq _ _ _ _
    (pairedMasses_odd_pow_sum_le_alternating T hn) heq k
  · intro x hx
    exact ⟨pairedMasses_nonneg T x hx, (pairedMasses_lt_half T hn x hx).trans (by norm_num)⟩
  · intro x hx
    exact ⟨pairedMasses_nonneg (alternatingTournament n) x hx,
      (pairedMasses_lt_half (alternatingTournament n) hn x hx).trans (by norm_num)⟩

/-- Spectral-ratio equality forces the fourth-order/Frobenius-square equality.
The p=3 odd moment supplies the bridge, then equality descends to p=2. -/
theorem sign_frob_sq_eq_of_spectralRatio_eq {n : ℕ} (hn : 2 ≤ n) (T : Tournament n)
    (heq : spectralRatio T = spectralRatio (alternatingTournament n)) :
    matrixFrobSq ((signMatrix T) ^ 2) =
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 2) := by
  apply sign_frob_sq_eq_of_pairedMasses_pow_eq hn T 3 (by norm_num)
  simpa using pairedMasses_odd_pow_eq_of_spectralRatio_eq T (by omega) heq 1

/-- Strictness at Frobenius exponent two forces a strictly smaller actual
spectral ratio. The fourth-order classification is a separate input. -/
theorem spectralRatio_lt_of_sign_frob_sq_lt {n : ℕ} (hn : 2 ≤ n) (T : Tournament n)
    (hlt : matrixFrobSq ((signMatrix T) ^ 2) <
      matrixFrobSq ((transitiveSkew n : Matrix (Fin n) (Fin n) ℝ) ^ 2)) :
    spectralRatio T < spectralRatio (alternatingTournament n) := by
  apply spectralRatio_lt_of_odd_paired_moments T (alternatingTournament n) (by omega)
    (pairedMasses_odd_pow_sum_le_alternating T (by omega)) 1
  simpa using pairedMasses_pow_lt_of_sign_frob_sq_lt hn T 3 (by norm_num) hlt

end TournamentHamiltonian
