module

public import TournamentHamiltonian.Equality.SwitchingBasics

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian.Equality

/-- A four-minor-one skew sign matrix with a dominating vertex has no directed triangle. -/
theorem no_triangle_of_allFourDetOne_of_pivot {ι : Type*}
    {S : Matrix ι ι ℝ} (hS : IsSkewSign S) (h4 : AllFourDetOne S)
    (p : ι) (hp : ∀ i, i ≠ p → S p i = 1) :
    ∀ i j k, S i j = 1 → S j k = 1 → S k i ≠ 1 := by
  intro i j k hij hjk hki
  have hi_ne_j : i ≠ j := by intro h; subst j; simp [hS.diag] at hij
  have hj_ne_k : j ≠ k := by intro h; subst k; simp [hS.diag] at hjk
  have hk_ne_i : k ≠ i := by intro h; subst i; simp [hS.diag] at hki
  have hi_ne_p : i ≠ p := by
    intro h; subst i
    have := hp k hk_ne_i
    have := hS.skew k p
    linarith
  have hj_ne_p : j ≠ p := by
    intro h; subst j
    have := hp i hi_ne_j
    have := hS.skew i p
    linarith
  have hk_ne_p : k ≠ p := by
    intro h; subst k
    have := hp j hj_ne_k
    have := hS.skew j p
    linarith
  let f : Fin 4 → ι := ![p, i, j, k]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp_all [f, Ne.symm hi_ne_p, Ne.symm hj_ne_p, Ne.symm hk_ne_p,
        Ne.symm hi_ne_j, Ne.symm hj_ne_k, Ne.symm hk_ne_i]
  have hik : S i k = -1 := by rw [hS.skew i k, hki]
  have hdet : (S.submatrix f f).det = 9 := by
    rw [det_skew_four (S.submatrix f f) (fun a b => hS.skew (f a) (f b))]
    norm_num [f, Matrix.submatrix_apply, hp i hi_ne_p, hp j hj_ne_p,
      hp k hk_ne_p, hij, hjk, hik]
  have := h4 f hf
  linarith

/-- The no-triangle tournament relation is transitive, without assuming any ordering. -/
theorem transitive_of_no_triangle {ι : Type*} {S : Matrix ι ι ℝ} (hS : IsSkewSign S)
    (htri : ∀ i j k, S i j = 1 → S j k = 1 → S k i ≠ 1) :
    (∀ i j k, S i j = 1 → S j k = 1 → S i k = 1) := by
  intro i j k hij hjk
  have hik : i ≠ k := by
    intro h; subst k
    have := hS.skew i j
    linarith
  rcases hS.signs i k hik with h | h
  · exact h
  · have hki : S k i = 1 := by have := hS.skew k i; linarith
    exact (htri i j k hij hjk hki).elim

/-- Finite tournament acyclicity is used here only through its explicit strict total order. -/
theorem strictTotalOrder_of_transitive {ι : Type*} {S : Matrix ι ι ℝ}
    (hS : IsSkewSign S) (htrans : (∀ i j k, S i j = 1 → S j k = 1 → S i k = 1)) :
    IsStrictTotalOrder ι (fun i j => S i j = 1) where
  irrefl i h := by simp [hS.diag] at h
  trans i j k := htrans i j k
  trichotomous i j := by
    intro hnij hnji
    by_contra hij
    rcases hS.signs i j hij with h | h
    · exact hnij h
    · apply hnji
      have := hS.skew j i
      linarith

/-- Pivot switching plus fourth principal minors constructs a strict total order. -/
theorem pivot_switch_strictTotalOrder {ι : Type*} [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : IsSkewSign S) (h4 : AllFourDetOne S) (p : ι) :
    IsStrictTotalOrder ι (fun i j => switch S (pivotSigns S p) i j = 1) := by
  have hε := pivotSigns_signs hS p
  have hs := hS.switch (pivotSigns S p) hε
  have hεsq : ∀ i, pivotSigns S p i ^ 2 = 1 := by
    intro i; rcases hε i with h | h <;> rw [h] <;> norm_num
  have h4s := (allFourDetOne_switch_iff S (pivotSigns S p) hεsq).mpr h4
  exact strictTotalOrder_of_transitive hs
    (transitive_of_no_triangle hs
      (no_triangle_of_allFourDetOne_of_pivot hs h4s p (switch_pivot_row hS p)))

end TournamentHamiltonian.Equality
