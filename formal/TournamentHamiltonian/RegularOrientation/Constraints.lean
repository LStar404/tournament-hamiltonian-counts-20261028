module

public import TournamentHamiltonian.RegularOrientation.Polynomial

@[expose] public section

set_option autoImplicit false

namespace RegularOrientation
open TournamentHamiltonian UniformBlowup MvPolynomial
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual required directed arcs, with at most one direction prescribed for
each canonical unordered edge. The selected set need not be a forest. -/
def Contains {m : ℕ} (T : Tournament m) (s : Finset (Edge m)) (a : Orientation m) : Prop :=
  ∀ e ∈ s, T.val (winner a e) (loser a e) = true

theorem prescribed_arc_iff_bit {m : ℕ} (T : Tournament m) (a : Orientation m) (e : Edge m) :
    T.val (winner a e) (loser a e) = true ↔ tournamentBits T e = a e := by
  cases ha : a e
  · have hr := T.property.2 e.val.2 e.val.1 (ne_of_gt e.property)
    simp only [winner, loser, ha, Bool.false_eq_true, ite_false, tournamentBits]
    rw [hr]
    cases h : T.val e.val.1 e.val.2 <;> simp
  · simp [winner, loser, ha, tournamentBits]

theorem contains_iff_bits {m : ℕ} (T : Tournament m) (s : Finset (Edge m)) (a : Orientation m) :
    Contains T s a ↔ ∀ e ∈ s, tournamentBits T e = a e := by
  simp only [Contains, prescribed_arc_iff_bit]

theorem contains_internal_iff {m : ℕ} (ω : Orientation m) (s : Finset (Edge m)) (a : Orientation m) :
    Contains (internalTournament ω) s a ↔ ∀ e ∈ s, ω e = a e := by
  rw [contains_iff_bits]
  have h : tournamentBits (internalTournament ω) = ω := (tournamentEquiv m).left_inv ω
  rw [h]

/-- Forced factors are winner monomials; unforced factors keep both choices.
No natural-number subtraction of exponent vectors occurs. -/
def constrainedPolynomial {m : ℕ} (s : Finset (Edge m)) (a : Orientation m) : MvPolynomial (Fin m) ℕ :=
  ∏ e : Edge m, if e ∈ s then X (winner a e) else X e.val.1 + X e.val.2

/-- The requested tail-monomial prefactor times the product with selected edges deleted. -/
theorem constrainedPolynomial_factorization {m : ℕ} (s : Finset (Edge m)) (a : Orientation m) :
    constrainedPolynomial s a =
      (∏ e ∈ s, (X (winner a e) : MvPolynomial (Fin m) ℕ)) *
        ∏ e ∈ sᶜ, (X e.val.1 + X e.val.2) := by
  rw [constrainedPolynomial, Finset.prod_ite]
  have hs : (Finset.univ.filter (fun e : Edge m => e ∈ s)) = s := by ext e; simp
  have hn : (Finset.univ.filter (fun e : Edge m => e ∉ s)) = sᶜ := by ext e; simp
  rw [hs, hn]

def localFactor {m : ℕ} (s : Finset (Edge m)) (a : Orientation m) (e : Edge m) (b : Bool) :
    MvPolynomial (Fin m) ℕ :=
  if e ∈ s then
    if b = a e then X (if b then e.val.1 else e.val.2) else 0
  else X (if b then e.val.1 else e.val.2)

theorem sum_localFactor {m : ℕ} (s : Finset (Edge m)) (a : Orientation m) (e : Edge m) :
    (∑ b : Bool, localFactor s a e b) =
      if e ∈ s then X (winner a e) else X e.val.1 + X e.val.2 := by
  by_cases he : e ∈ s <;> cases ha : a e <;>
    simp [localFactor, winner, he, ha, Fintype.univ_bool]

theorem prod_localFactor {m : ℕ} (s : Finset (Edge m)) (a ω : Orientation m) :
    (∏ e : Edge m, localFactor s a e (ω e)) =
      if (∀ e ∈ s, ω e = a e) then monomial (winnerExponent ω) 1 else 0 := by
  by_cases h : ∀ e ∈ s, ω e = a e
  · rw [ite_eq_left h, ← prod_winner_X]
    apply Finset.prod_congr rfl
    intro e _
    by_cases he : e ∈ s
    · simp [localFactor, he, h e he, winner]
    · simp [localFactor, he, winner]
  · rw [ite_eq_right h]
    obtain ⟨e, he, hne⟩ : ∃ e, e ∈ s ∧ ω e ≠ a e := by
      by_contra hh
      apply h
      intro e he
      by_contra hne
      exact hh ⟨e, he, hne⟩
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [localFactor, he, hne])

theorem constrainedPolynomial_eq_sum_bits {m : ℕ} (s : Finset (Edge m)) (a : Orientation m) :
    constrainedPolynomial s a = ∑ ω : Orientation m,
      if (∀ e ∈ s, ω e = a e) then monomial (winnerExponent ω) 1 else 0 := by
  conv_lhs => simp only [constrainedPolynomial, ← sum_localFactor s a]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact prod_localFactor s a ω

/-- Complete constrained generating-function identity over actual tournaments. -/
theorem constrainedPolynomial_eq_sum_tournaments {m : ℕ} (s : Finset (Edge m)) (a : Orientation m) :
    constrainedPolynomial s a = ∑ T : Tournament m,
      if Contains T s a then monomial (outVector T) 1 else 0 := by
  rw [constrainedPolynomial_eq_sum_bits]
  apply Fintype.sum_equiv (tournamentEquiv m)
  intro ω
  change _ = if Contains (internalTournament ω) s a then _ else _
  rw [contains_internal_iff, winnerExponent_eq_outVector]
  split_ifs <;> rfl

/-- Exact constrained coefficient count, valid for every exponent vector and
arbitrary consistent prescribed edges, not only forests. -/
theorem constrainedPolynomial_coeff {m : ℕ} (s : Finset (Edge m)) (a : Orientation m)
    (r : Exponent m) :
    (constrainedPolynomial s a).coeff r =
      (Finset.univ.filter (fun T : Tournament m => Contains T s a ∧ outVector T = r)).card := by
  rw [constrainedPolynomial_eq_sum_tournaments, coeff_sum]
  trans ∑ T : Tournament m, if Contains T s a ∧ outVector T = r then (1 : ℕ) else 0
  · apply Finset.sum_congr rfl
    intro T _
    by_cases hc : Contains T s a <;> simp [hc, coeff_monomial]
  · simp

end
end RegularOrientation
