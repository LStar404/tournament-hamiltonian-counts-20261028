module

public import TournamentHamiltonian.UniformSpectralUpper
public import TournamentHamiltonian.OperatorCap
public import TournamentHamiltonian.CarouselPathLower

@[expose] public section

/-! The actual finite supremum and one common pair of constants in Proposition 7.1. -/
noncomputable section
namespace PaperEndpointWrappersB
open TournamentHamiltonian Filter

/-- The elementary spectral cap applied to every actual maximizing tournament. -/
theorem maxPaths_upper_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (maxPaths n : ℝ) ≤ (upperConstant + C / n) * meanPaths n := by
  obtain ⟨C, hC, h⟩ := actual_uniform_pathCount_spectral_upper
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨C, hC, max N 2, le_max_right _ _, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  classical
  obtain ⟨T, _hT, hmax⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Tournament n))
    ⟨alternatingTournament n, Finset.mem_univ _⟩ pathCount
  change maxPaths n = pathCount T at hmax
  have hp := hN n hnN T
  have hs := spectralRatio_le_upperConstant T hnpos
  rw [hmax]
  exact (div_le_iff₀ (by unfold meanPaths; positivity : 0 < meanPaths n)).mp
    (hp.trans (add_le_add hs le_rfl))

/-- Proposition 7.1: a proved proposition, not merely the `MainBound` definition.
The same K and threshold serve both sides of the actual finite maximum. -/
theorem mainBound : MainBound := by
  obtain ⟨Cl, hCl, Nl, hNl, hl⟩ := maxPaths_lower_uniform
  obtain ⟨Cu, hCu, Nu, _hNu, hu⟩ := maxPaths_upper_uniform
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

/-- The two explicit manuscript constants and factorial normalization. -/
theorem proposition7_1 :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (Real.cosh 1 / Real.cos 1 - K / n) * ((n.factorial : ℝ) / 2 ^ (n - 1)) ≤
        (maxPaths n : ℝ) ∧
      (maxPaths n : ℝ) ≤
        ((3 * Real.pi ^ 4 + 4 * Real.pi ^ 2 - 32) /
          (Real.pi ^ 4 + 4 * Real.pi ^ 2 - 32) + K / n) *
            ((n.factorial : ℝ) / 2 ^ (n - 1)) := by
  simpa only [MainBound, lowerConstant, upperConstant, meanPaths] using mainBound

end PaperEndpointWrappersB
