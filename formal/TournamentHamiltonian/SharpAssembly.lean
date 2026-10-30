module

public import Tournament.SharpBound
public import TournamentHamiltonian.CarouselPathLower
public import TournamentHamiltonian.UniformSpectralUpper
public import TournamentHamiltonian.SharpSpectralMoments

/-!
# Conditional assembly with its finite matrix comparison visible

The theorem below is deliberately conditional.  Its sole additional premise
is the all-order, all-odd-moment comparison for actual tournament matrices.
`FrobeniusComparison` proves that premise and `SharpMain` instantiates it.
This module keeps the conditional assembly separate from its finite proof.
It records that no permanent, scaling, error, parity, or extremum premise
remains once the displayed finite matrix comparison is supplied.
-/

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open Filter
open scoped Classical

theorem sharpMainBound_of_odd_paired_moments
    (hmoments : ∀ n : ℕ, 2 ≤ n → ∀ T : Tournament n, ∀ k : ℕ,
      ((pairedMasses T).map (fun x => x ^ (2 * k + 1))).sum ≤
        ((pairedMasses (alternatingTournament n)).map (fun x => x ^ (2 * k + 1))).sum) :
    SharpMainBound := by
  obtain ⟨Ca, hCa, ha⟩ := actual_uniform_pathCount_spectral_upper
  obtain ⟨Na, hNa⟩ := eventually_atTop.mp ha
  obtain ⟨Cs, hCs, Ns, _hNs, hs⟩ := alternating_spectralRatio_error_bound
  have hupper : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (maxPaths n : ℝ) ≤ (lowerConstant + C / n) * meanPaths n := by
    refine ⟨Ca + Cs, add_nonneg hCa hCs, max (max Na Ns) 2, le_max_right _ _, ?_⟩
    intro n hn
    have hnNa : Na ≤ n := (le_trans (le_max_left Na Ns) (le_max_left _ _)).trans hn
    have hnNs : Ns ≤ n := (le_trans (le_max_right Na Ns) (le_max_left _ _)).trans hn
    have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    have hn0 : 0 < n := by omega
    classical
    obtain ⟨T, _hT, hmax⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Tournament n))
      ⟨alternatingTournament n, Finset.mem_univ _⟩ pathCount
    change maxPaths n = pathCount T at hmax
    have hpath := hNa n hnNa T
    have hspec := spectralRatio_le_of_odd_paired_moments T (alternatingTournament n) hn0
      (hmoments n hn2 T)
    have hnear := (abs_le.mp (hs n hnNs)).2
    have hnorm : (pathCount T : ℝ) / meanPaths n ≤ lowerConstant + (Ca + Cs) / n := by
      rw [add_div]
      linarith
    rw [hmax]
    exact (div_le_iff₀ (by unfold meanPaths; positivity : 0 < meanPaths n)).mp hnorm
  obtain ⟨Cl, hCl, Nl, hNl, hl⟩ := maxPaths_lower_uniform
  obtain ⟨Cu, hCu, Nu, _hNu, hu⟩ := hupper
  refine ⟨Cl + Cu, add_nonneg hCl hCu, max Nl Nu, hNl.trans (le_max_left _ _), ?_⟩
  intro n hn
  have hnNl : Nl ≤ n := (le_max_left _ _).trans hn
  have hnNu : Nu ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm : 0 ≤ meanPaths n := by unfold meanPaths; positivity
  have hL : Cl / (n : ℝ) ≤ (Cl + Cu) / n :=
    div_le_div_of_nonneg_right (by linarith) hn0
  have hU : Cu / (n : ℝ) ≤ (Cl + Cu) / n :=
    div_le_div_of_nonneg_right (by linarith) hn0
  constructor
  · exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hL lowerConstant) hm).trans (hl n hnNl)
  · exact (hu n hnNu).trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl _) hU) hm)

end TournamentHamiltonian
