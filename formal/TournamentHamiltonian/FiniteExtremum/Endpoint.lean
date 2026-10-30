module

public import TournamentHamiltonian.FiniteExtremum.Comparison

@[expose] public section

set_option autoImplicit false
namespace FiniteExtremum
open TournamentHamiltonian UniformBlowup NonregularDecay FiniteFamilyGap Filter
noncomputable section

/-- Actual four-model eventual unique maximization up to ordinary base isomorphism.
The uniform assertion ranges over every sufficiently large m; regular blocks are
exactly 2k+1. Every limit and every strict finite-family gap is proved upstream,
not supplied as a caller hypothesis. The singleton order also satisfies this. -/
theorem eventual_four_models (h : ℕ) :
    ∃ M : ℕ, 0 < M ∧
      (∀ m : ℕ, M ≤ m → UniformMaximumAt h m) ∧
      (∀ k : ℕ, M ≤ 2*k+1 → RegularMaximumAt h k) := by
  obtain ⟨U,hU⟩ := Filter.eventually_atTop.mp (uniform_maximum_eventually h)
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp (regular_maximum_eventually h)
  refine ⟨commonThreshold U K, commonThreshold_pos U K, ?_, ?_⟩
  · intro m hm
    exact hU m (uniform_index_of_commonThreshold hm)
  · intro k hk
    exact hK k (regular_index_of_commonThreshold hk)

/-- Equivalent ordinary-m statement: the regular assertion has the explicit odd
block-size guard, and k=m/2 is the actual existing regular sample parameter. -/
theorem eventual_four_models_odd_blocks (h : ℕ) :
    ∃ M : ℕ, 0 < M ∧
      (∀ m : ℕ, M ≤ m → UniformMaximumAt h m) ∧
      (∀ m : ℕ, M ≤ m → Odd m → RegularMaximumAt h (m/2)) := by
  obtain ⟨M,hM,hU,hR⟩ := eventual_four_models h
  refine ⟨M,hM,hU,?_⟩
  intro m hm ho
  obtain ⟨k,hk⟩ := ho
  have he : m=2*k+1 := by omega
  have hd : m/2=k := by omega
  rw [hd]
  exact hR k (by omega)

/-- Literal fixed-odd-order quantifiers of Corollaries 1.3/11.2. The equality
identifies the actual index type with Fin d; no uniformity in a growing d is claimed. -/
theorem eventual_four_models_of_odd (d : ℕ) (hd : Odd d) (hd3 : 3≤d) :
    ∃ h : ℕ, d=2*h+1 ∧ 1≤h ∧ ∃ M : ℕ, 0<M ∧
      (∀ m : ℕ, M≤m → UniformMaximumAt h m) ∧
      (∀ m : ℕ, M≤m → Odd m → RegularMaximumAt h (m/2)) := by
  obtain ⟨h,hh⟩ := hd
  refine ⟨h,by omega,by omega,?_⟩
  exact eventual_four_models_odd_blocks h

/-- Strict exclusion is also explicit, not only recoverable from equality cases. -/
theorem eventual_four_strict_outside (h : ℕ) :
    ∃ M : ℕ, 0<M ∧
    (∀ m : ℕ, M≤m → ∀ T : Tournament (2*h+1), ¬CarouselClass h T →
      avgCycle (m:=m) T < avgCycle (m:=m) (carouselTournament h) ∧
      avgPath (m:=m) T < avgPath (m:=m) (carouselTournament h)) ∧
    (∀ k : ℕ, M≤2*k+1 → ∀ T : Tournament (2*h+1), ¬CarouselClass h T →
      regularAvgCycle T k < regularAvgCycle (carouselTournament h) k ∧
      regularAvgPath T k < regularAvgPath (carouselTournament h) k) := by
  obtain ⟨U,hU⟩ := Filter.eventually_atTop.mp (uniform_outside_eventually h)
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp (regular_outside_eventually h)
  exact ⟨commonThreshold U K,commonThreshold_pos U K,
    fun m hm => hU m (uniform_index_of_commonThreshold hm),
    fun k hk => hK k (regular_index_of_commonThreshold hk)⟩

end
end FiniteExtremum
