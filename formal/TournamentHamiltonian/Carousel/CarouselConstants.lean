module
public import TournamentHamiltonian.SkewSpectrum
public import TournamentHamiltonian.TransitiveCotSpectrum
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section
namespace TournamentHamiltonian
open Filter Topology

/-- The regular-internal-block constant of the actual odd carousel of order `2*m+1`. -/
noncomputable def regularCarouselConstant (m : ℕ) : ℝ :=
  Real.exp (1 / (2 * (m : ℝ) + 1)) * spectralRatio (carouselTournament m)

theorem regularCarouselConstant_pos (m : ℕ) : 0 < regularCarouselConstant m :=
  mul_pos (Real.exp_pos _) (spectralRatio_bounds _ (by omega)).1

/-- Exact polynomial closed form; its ratio is the genuine carousel spectral ratio. -/
theorem regularCarouselConstant_closed_form (m : ℕ) :
    (regularCarouselConstant m : ℂ) =
      (Real.exp (1 / (2 * (m : ℝ) + 1)) : ℂ) *
      (((1 + 1 / (2 * (m : ℂ) + 1)) ^ (2 * m + 1) +
        (1 - 1 / (2 * (m : ℂ) + 1)) ^ (2 * m + 1)) /
       ((1 + Complex.I / (2 * (m : ℂ) + 1)) ^ (2 * m + 1) +
        (1 - Complex.I / (2 * (m : ℂ) + 1)) ^ (2 * m + 1))) := by
  rw [regularCarouselConstant, Complex.ofReal_mul, carousel_spectralRatio_eq,
    transitiveRatio_eq_binomialMean]
  simp only [binomialMean, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  congr 1
  exact div_div_div_cancel_right₀ (by norm_num : (2 : ℂ) ≠ 0) _ _

private theorem oddOrder_tendsto :
    Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop := by
  apply tendsto_atTop_mono (f := fun m : ℕ => m) (fun m => by omega) tendsto_id

private theorem inv_oddOrder_tendsto :
    Tendsto (fun m : ℕ => 1 / (2 * (m : ℝ) + 1)) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ) |>.comp oddOrder_tendsto)
  simpa [one_div, Function.comp_def] using h

theorem carousel_spectralRatio_tendsto :
    Tendsto (fun m : ℕ => spectralRatio (carouselTournament m)) atTop (𝓝 lowerConstant) := by
  have h := Complex.continuous_re.tendsto _ |>.comp
    (transitiveRatio_tendsto.comp oddOrder_tendsto)
  simpa only [Function.comp_def, ← carousel_spectralRatio_eq, Complex.ofReal_re] using h

/-- The actual regular-carousel constants converge to the manuscript's `L`. -/
theorem regularCarouselConstant_tendsto :
    Tendsto regularCarouselConstant atTop (𝓝 (Real.cosh 1 / Real.cos 1)) := by
  change Tendsto (fun m : ℕ => Real.exp (1 / (2 * (m : ℝ) + 1)) * spectralRatio (carouselTournament m)) atTop _
  have he := Real.continuous_exp.tendsto 0 |>.comp inv_oddOrder_tendsto
  have h := he.mul carousel_spectralRatio_tendsto
  simpa only [Real.exp_zero, one_mul, regularCarouselConstant, lowerConstant, Function.comp_def] using h

end TournamentHamiltonian
