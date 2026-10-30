module

public import TournamentHamiltonian.FiniteFamilyGap.Scores

@[expose] public section

set_option autoImplicit false
namespace FiniteFamilyGap
open TournamentHamiltonian UniformBlowup NonregularDecay
noncomputable section
attribute [local instance] Classical.propDecidable

/-- All actual labelled bases outside the ordinary carousel isomorphism class. -/
def outsideFamily (h : ℕ) : Finset (Tournament (2*h+1)) :=
  Finset.univ.filter (fun T => ¬CarouselClass h T)

@[simp] theorem mem_outsideFamily (h : ℕ) (T : Tournament (2*h+1)) :
    T ∈ outsideFamily h ↔ ¬CarouselClass h T := by simp [outsideFamily]

theorem carousel_not_mem (h : ℕ) : carouselTournament h ∉ outsideFamily h := by
  simp [carousel_class_self]

/-- A single explicit positive constant handles both model limiting expressions. -/
def commonGap (h : ℕ) : ℝ :=
  min (spectralGap h) (Real.exp (1 / ((2*h+1:ℕ):ℝ)) * spectralGap h)

theorem commonGap_pos (h : ℕ) : 0 < commonGap h :=
  lt_min (spectralGap_pos h) (mul_pos (Real.exp_pos _) (spectralGap_pos h))

theorem commonGap_le_both_deficits (h : ℕ) (T : Tournament (2*h+1))
    (hT : T ∈ outsideFamily h) :
    commonGap h ≤ uniformScore (carouselTournament h) - uniformScore T ∧
    commonGap h ≤ regularScore (carouselTournament h) - regularScore T := by
  have hg := spectralGap_le_uniform_deficit h T ((mem_outsideFamily h T).mp hT)
  constructor
  · exact (min_le_left _ _).trans hg
  · exact (min_le_right _ _).trans (by
      simpa only [regularScore, mul_sub] using
        mul_le_mul_of_nonneg_left hg (Real.exp_pos (1 / ((2*h+1:ℕ):ℝ))).le)

theorem finite_common_score_gap (h : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T ∈ outsideFamily h,
      uniformScore T + ε ≤ uniformScore (carouselTournament h) ∧
      regularScore T + ε ≤ regularScore (carouselTournament h) := by
  refine ⟨commonGap h, commonGap_pos h, ?_⟩
  intro T hT
  obtain ⟨hu,hr⟩ := commonGap_le_both_deficits h T hT
  constructor <;> linarith

/-- Equality on the ordinary class is an exact finite expectation identity,
not merely a limiting statement. -/
theorem four_expectations_sameclass (h : ℕ) (T : Tournament (2*h+1))
    (hT : CarouselClass h T) (m k : ℕ) :
    avgPath (m:=m) T = avgPath (m:=m) (carouselTournament h) ∧
    avgCycle (m:=m) T = avgCycle (m:=m) (carouselTournament h) ∧
    regularAvgPath T k = regularAvgPath (carouselTournament h) k ∧
    regularAvgCycle T k = regularAvgCycle (carouselTournament h) k :=
  BaseRelabel.four_expectations_eq_of_relabel T (carouselTournament h) hT m k

/-- Pure index bookkeeping: the first bound applies to every m, the second
only to the genuine regular model parameter m=2k+1. No limit is presumed. -/
def commonThreshold (uniformM regularK : ℕ) : ℕ :=
  max 1 (max uniformM (2*regularK+1))

theorem commonThreshold_pos (uniformM regularK : ℕ) :
    0 < commonThreshold uniformM regularK := by
  unfold commonThreshold
  omega

theorem uniform_index_of_commonThreshold {uniformM regularK m : ℕ}
    (hm : commonThreshold uniformM regularK ≤ m) : uniformM ≤ m := by
  unfold commonThreshold at hm
  omega

theorem regular_index_of_commonThreshold {uniformM regularK k : ℕ}
    (hk : commonThreshold uniformM regularK ≤ 2*k+1) : regularK ≤ k := by
  unfold commonThreshold at hk
  omega

/-- Convert arbitrary odd m back to the existing k-indexed regular expectation,
without restricting the uniform model to odd indices. -/
theorem odd_index_of_commonThreshold {uniformM regularK m : ℕ} (hm : Odd m)
    (hM : commonThreshold uniformM regularK ≤ m) :
    ∃ k : ℕ, m = 2*k+1 ∧ regularK ≤ k := by
  obtain ⟨k,hk⟩ := hm
  refine ⟨k, by omega, ?_⟩
  apply regular_index_of_commonThreshold (uniformM:=uniformM)
  omega

end
end FiniteFamilyGap
