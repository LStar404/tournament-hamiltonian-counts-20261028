module
public import TournamentHamiltonian.Carousel.PositiveMoments
public import TournamentHamiltonian.Carousel.LogCancellation

@[expose] public section
namespace TournamentHamiltonian
open Filter Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual regular-block carousel constants strictly increase at every odd order. -/
theorem regularCarouselConstant_strictMono : StrictMono regularCarouselConstant := by
  apply strictMono_nat_of_lt_succ
  intro m
  apply (Real.log_lt_log_iff (regularCarouselConstant_pos m)
    (regularCarouselConstant_pos (m+1))).mp
  apply (sub_lt_sub_iff_right (1 : ℝ)).mp
  have hterm (k : ℕ) :
      (2 : ℝ) * (1 / (2*((k+1 : ℕ) : ℝ)+1)) *
          ((pairedMasses (transitiveTournament (2*m+1))).map (fun x => x^(2*(k+1)+1))).sum <
      (2 : ℝ) * (1 / (2*((k+1 : ℕ) : ℝ)+1)) *
          ((pairedMasses (transitiveTournament (2*(m+1)+1))).map (fun x => x^(2*(k+1)+1))).sum := by
    exact mul_lt_mul_of_pos_left
      (transitive_pairedMoments_lt_succ m (2*(k+1)+1) (by omega)) (by positivity)
  exact hasSum_lt (fun k => (hterm k).le) (hterm 0)
    (regularCarouselConstant_hasSum_log_tail m)
    (regularCarouselConstant_hasSum_log_tail (m+1))

/-- Every finite odd-order regular carousel constant lies strictly below `L`. -/
theorem regularCarouselConstant_lt_limit (m : ℕ) :
    regularCarouselConstant m < Real.cosh 1 / Real.cos 1 := by
  have hb : regularCarouselConstant (m+1) ≤ Real.cosh 1 / Real.cos 1 := by
    apply ge_of_tendsto regularCarouselConstant_tendsto
    filter_upwards [eventually_ge_atTop (m+1)] with k hk
    exact regularCarouselConstant_strictMono.monotone hk
  exact (regularCarouselConstant_strictMono (by omega : m < m+1)).trans_le hb

/-- Corollary 10.5, joined as one unconditional theorem for the genuine constants.
In particular, restricting to `m ≥ 1` gives exactly odd orders `d ≥ 3`. -/
theorem regularCarouselConstant_monotone_convergent :
    StrictMono regularCarouselConstant ∧
      Tendsto regularCarouselConstant atTop (𝓝 (Real.cosh 1 / Real.cos 1)) ∧
      (∀ m : ℕ, regularCarouselConstant m < Real.cosh 1 / Real.cos 1) :=
  ⟨regularCarouselConstant_strictMono, regularCarouselConstant_tendsto,
    regularCarouselConstant_lt_limit⟩

end TournamentHamiltonian
