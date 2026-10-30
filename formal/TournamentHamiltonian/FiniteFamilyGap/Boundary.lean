module

public import TournamentHamiltonian.FiniteFamilyGap.Finite

@[expose] public section

set_option autoImplicit false
namespace FiniteFamilyGap
open TournamentHamiltonian TournamentHamiltonian.Equality RegularOrientation
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The one-vertex boundary has no outside bases; the positive gap still causes no issue. -/
theorem outsideFamily_zero : outsideFamily 0 = ∅ := by
  apply Finset.ext
  intro T
  have he : T = carouselTournament 0 := tournament_eq_of_card_le_one (by norm_num) _ _
  subst T
  simp [carousel_class_self]

theorem commonGap_zero_pos : 0 < commonGap 0 := commonGap_pos 0

theorem commonThreshold_zero_zero : commonThreshold 0 0 = 1 := by
  norm_num [commonThreshold]

/-- The uniform threshold really permits an even index. -/
theorem even_uniform_index : commonThreshold 2 0 ≤ 2 ∧ 2 ≤ 2 := by
  norm_num [commonThreshold]

theorem odd_threshold_conversion {m : ℕ} (hm : Odd m) (hM : 11 ≤ m) :
    ∃ k : ℕ, m = 2*k+1 ∧ 5 ≤ k := by
  apply odd_index_of_commonThreshold (uniformM:=4)
  · exact hm
  · simpa [commonThreshold] using hM

/-- A concrete nonregular spectral extremizer: this is why score zero is essential. -/
theorem transitive_three_nonregular : ¬IsRegular (transitiveTournament 3) := by
  intro h
  have he := h (0 : Fin 3)
  norm_num [score, signMatrix, transitiveTournament, Fin.sum_univ_succ] at he

theorem transitive_three_not_carousel : ¬CarouselClass 1 (transitiveTournament 3) := by
  intro h
  exact transitive_three_nonregular (regular_of_carouselClass h)

theorem transitive_three_spectral_equal :
    spectralRatio (transitiveTournament 3) = spectralRatio (carouselTournament 1) := by
  rw [carousel_spectralRatio_eq_alternating]
  apply (spectralRatio_eq_iff_signedPermutationTransitive _).mpr
  refine ⟨fun _ => 1, fun _ => Or.inl rfl, Equiv.refl _, ?_⟩
  simp [switch, signMatrix_transitiveTournament, Matrix.submatrix]
  rfl

theorem transitive_three_scores_zero :
    uniformScore (transitiveTournament 3) = 0 ∧ regularScore (transitiveTournament 3) = 0 :=
  ⟨uniformScore_of_nonregular _ transitive_three_nonregular,
    regularScore_of_nonregular _ transitive_three_nonregular⟩

theorem transitive_three_both_strict :
    uniformScore (transitiveTournament 3) < uniformScore (carouselTournament 1) ∧
    regularScore (transitiveTournament 3) < regularScore (carouselTournament 1) :=
  ⟨(uniformScore_lt_iff_not_carouselClass _ _).mpr transitive_three_not_carousel,
    (regularScore_lt_iff_not_carouselClass _ _).mpr transitive_three_not_carousel⟩

end
end FiniteFamilyGap
