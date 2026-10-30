module

public import TournamentHamiltonian.FiniteExtremum.Endpoint
public import TournamentHamiltonian.BaseRelabel.Boundary

@[expose] public section

set_option autoImplicit false
namespace FiniteExtremum
open TournamentHamiltonian TournamentHamiltonian.Equality UniformBlowup NonregularDecay
  RegularOrientation FiniteFamilyGap
noncomputable section
attribute [local instance] Classical.propDecidable

theorem singleton_uniform_all_sizes (m : ℕ) : UniformMaximumAt 0 m := by
  intro T
  have he : T=carouselTournament 0 := tournament_eq_of_card_le_one (by norm_num) _ _
  subst T
  simp [carousel_class_self]

theorem singleton_regular_all_sizes (k : ℕ) : RegularMaximumAt 0 k := by
  intro T
  have he : T=carouselTournament 0 := tournament_eq_of_card_le_one (by norm_num) _ _
  subst T
  simp [carousel_class_self]

theorem order_three_four_models :
    ∃ M : ℕ, 0<M ∧ (∀ m : ℕ, M≤m → UniformMaximumAt 1 m) ∧
      (∀ k : ℕ, M≤2*k+1 → RegularMaximumAt 1 k) := eventual_four_models 1

/-- The uniform conclusion does include arbitrarily large even blocks. -/
theorem even_uniform_blocks (h : ℕ) :
    ∃ M : ℕ, 0<M ∧ ∀ k : ℕ, M≤2*k → UniformMaximumAt h (2*k) := by
  obtain ⟨M,hM,hU,-⟩ := eventual_four_models h
  exact ⟨M,hM,fun k hk => hU (2*k) hk⟩

theorem regular_order_ne_zero (k : ℕ) : 2*k+1 ≠ 0 := by omega

theorem zero_path_normalizer_positive : 0 < meanPaths 0 := meanPaths_pos 0

theorem zero_cycle_normalizer_positive : 0 < meanCycles 0 := NonregularDecay.meanCycles_pos 0

/-- Concrete nonregular exclusion at the smallest manuscript base order. -/
theorem transitive_three_outside : ¬CarouselClass 1 (transitiveTournament 3) := by
  intro hc
  have hr := regular_of_carouselClass hc (0 : Fin 3)
  norm_num [score,signMatrix,transitiveTournament,Fin.sum_univ_succ] at hr

theorem transitive_three_actual_strict :
    ∃ M : ℕ, 0<M ∧
      (∀ m : ℕ, M≤m →
        avgCycle (m:=m) (transitiveTournament 3) < avgCycle (m:=m) (carouselTournament 1) ∧
        avgPath (m:=m) (transitiveTournament 3) < avgPath (m:=m) (carouselTournament 1)) ∧
      (∀ k : ℕ, M≤2*k+1 →
        regularAvgCycle (transitiveTournament 3) k < regularAvgCycle (carouselTournament 1) k ∧
        regularAvgPath (transitiveTournament 3) k < regularAvgPath (carouselTournament 1) k) := by
  obtain ⟨M,hM,hU,hR⟩ := eventual_four_strict_outside 1
  exact ⟨M,hM,fun m hm => hU m hm _ transitive_three_outside,
    fun k hk => hR k hk _ transitive_three_outside⟩

/-- Zero-sized uniform blocks make all cycle expectations equal, including
nonisomorphic bases. Thus the eventual theorem cannot be replaced by an all-m claim. -/
theorem not_order_three_maximum_at_zero : ¬UniformMaximumAt 1 0 := by
  intro hm
  have hz (T : Tournament 3) : avgCycle (m:=0) T = 0 := by
    unfold avgCycle
    simp [BaseRelabel.cycleCount_empty_blocks]
  have hc := (hm (transitiveTournament 3)).1.2.mp
    (show avgCycle (m:=0) (transitiveTournament 3) = avgCycle (m:=0) (carouselTournament 1) by
      rw [hz, hz])
  exact transitive_three_outside hc

end
end FiniteExtremum
