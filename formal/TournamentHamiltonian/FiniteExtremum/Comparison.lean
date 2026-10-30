module

public import TournamentHamiltonian.FiniteExtremum.Limits

@[expose] public section

set_option autoImplicit false
namespace FiniteExtremum
open TournamentHamiltonian UniformBlowup NonregularDecay FiniteFamilyGap Filter
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every ordinary non-carousel base has both actual uniform expectations
strictly smaller, eventually with one index for the whole finite family. -/
theorem uniform_outside_eventually (h : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ T : Tournament (2*h+1), ¬CarouselClass h T →
      avgCycle (m:=m) T < avgCycle (m:=m) (carouselTournament h) ∧
      avgPath (m:=m) T < avgPath (m:=m) (carouselTournament h) := by
  have hc := Tournament.finite_eventual_unique_max (l:=atTop) (outsideFamily h)
    (fun T m => avgCycle (m:=m) T / meanCycles ((2*h+1)*m)) uniformScore
    (fun m => avgCycle (m:=m) (carouselTournament h) / meanCycles ((2*h+1)*m))
    (uniformScore (carouselTournament h))
    (fun T _ => uniform_cycle_limit T (by omega))
    (uniform_cycle_limit (carouselTournament h) (by omega))
    (fun T hT => (uniformScore_lt_iff_not_carouselClass h T).mpr ((mem_outsideFamily h T).mp hT))
  have hp := Tournament.finite_eventual_unique_max (l:=atTop) (outsideFamily h)
    (fun T m => avgPath (m:=m) T / meanPaths ((2*h+1)*m)) uniformScore
    (fun m => avgPath (m:=m) (carouselTournament h) / meanPaths ((2*h+1)*m))
    (uniformScore (carouselTournament h))
    (fun T _ => uniform_path_limit T (by omega))
    (uniform_path_limit (carouselTournament h) (by omega))
    (fun T hT => (uniformScore_lt_iff_not_carouselClass h T).mpr ((mem_outsideFamily h T).mp hT))
  filter_upwards [hc,hp] with m hc hp T hT
  have hm := (mem_outsideFamily h T).mpr hT
  exact ⟨(div_lt_div_iff_of_pos_right (NonregularDecay.meanCycles_pos _)).mp (hc T hm),
    (div_lt_div_iff_of_pos_right (meanPaths_pos _)).mp (hp T hm)⟩

/-- Actual regular expectations, with no hypothetical asymptotic premise. -/
theorem regular_outside_eventually (h : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ T : Tournament (2*h+1), ¬CarouselClass h T →
      regularAvgCycle T k < regularAvgCycle (carouselTournament h) k ∧
      regularAvgPath T k < regularAvgPath (carouselTournament h) k := by
  have hc := Tournament.finite_eventual_unique_max (l:=atTop) (outsideFamily h)
    (fun T k => regularAvgCycle T k / meanCycles ((2*h+1)*(2*k+1))) regularScore
    (fun k => regularAvgCycle (carouselTournament h) k / meanCycles ((2*h+1)*(2*k+1)))
    (regularScore (carouselTournament h))
    (fun T _ => regular_cycle_limit T (by omega))
    (regular_cycle_limit (carouselTournament h) (by omega))
    (fun T hT => (regularScore_lt_iff_not_carouselClass h T).mpr ((mem_outsideFamily h T).mp hT))
  have hp := Tournament.finite_eventual_unique_max (l:=atTop) (outsideFamily h)
    (fun T k => regularAvgPath T k / meanPaths ((2*h+1)*(2*k+1))) regularScore
    (fun k => regularAvgPath (carouselTournament h) k / meanPaths ((2*h+1)*(2*k+1)))
    (regularScore (carouselTournament h))
    (fun T _ => regular_path_limit T (by omega))
    (regular_path_limit (carouselTournament h) (by omega))
    (fun T hT => (regularScore_lt_iff_not_carouselClass h T).mpr ((mem_outsideFamily h T).mp hT))
  filter_upwards [hc,hp] with k hc hp T hT
  have hm := (mem_outsideFamily h T).mpr hT
  exact ⟨(div_lt_div_iff_of_pos_right (NonregularDecay.meanCycles_pos _)).mp (hc T hm),
    (div_lt_div_iff_of_pos_right (meanPaths_pos _)).mp (hp T hm)⟩

/-- Each actual uniform expectation is maximal exactly on the ordinary class. -/
def UniformMaximumAt (h m : ℕ) : Prop := ∀ T : Tournament (2*h+1),
  (avgCycle (m:=m) T ≤ avgCycle (m:=m) (carouselTournament h) ∧
    (avgCycle (m:=m) T = avgCycle (m:=m) (carouselTournament h) ↔ CarouselClass h T)) ∧
  (avgPath (m:=m) T ≤ avgPath (m:=m) (carouselTournament h) ∧
    (avgPath (m:=m) T = avgPath (m:=m) (carouselTournament h) ↔ CarouselClass h T))

def RegularMaximumAt (h k : ℕ) : Prop := ∀ T : Tournament (2*h+1),
  (regularAvgCycle T k ≤ regularAvgCycle (carouselTournament h) k ∧
    (regularAvgCycle T k = regularAvgCycle (carouselTournament h) k ↔ CarouselClass h T)) ∧
  (regularAvgPath T k ≤ regularAvgPath (carouselTournament h) k ∧
    (regularAvgPath T k = regularAvgPath (carouselTournament h) k ↔ CarouselClass h T))

theorem uniform_maximum_eventually (h : ℕ) : ∀ᶠ m : ℕ in atTop, UniformMaximumAt h m := by
  filter_upwards [uniform_outside_eventually h] with m hm T
  by_cases hc : CarouselClass h T
  · obtain ⟨hp,hcy,-,-⟩ := four_expectations_sameclass h T hc m 0
    exact ⟨⟨hcy.le, by simp [hcy,hc]⟩,⟨hp.le, by simp [hp,hc]⟩⟩
  · obtain ⟨hcy,hp⟩ := hm T hc
    exact ⟨⟨hcy.le, by simp [ne_of_lt hcy,hc]⟩,⟨hp.le, by simp [ne_of_lt hp,hc]⟩⟩

theorem regular_maximum_eventually (h : ℕ) : ∀ᶠ k : ℕ in atTop, RegularMaximumAt h k := by
  filter_upwards [regular_outside_eventually h] with k hk T
  by_cases hc : CarouselClass h T
  · obtain ⟨-,-,hp,hcy⟩ := four_expectations_sameclass h T hc 0 k
    exact ⟨⟨hcy.le, by simp [hcy,hc]⟩,⟨hp.le, by simp [hp,hc]⟩⟩
  · obtain ⟨hcy,hp⟩ := hk T hc
    exact ⟨⟨hcy.le, by simp [ne_of_lt hcy,hc]⟩,⟨hp.le, by simp [ne_of_lt hp,hc]⟩⟩

end
end FiniteExtremum
