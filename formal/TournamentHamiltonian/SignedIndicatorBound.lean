module

public import TournamentHamiltonian.ComparisonBudget

set_option autoImplicit false

@[expose] public section

namespace TournamentHamiltonian

open scoped BigOperators

theorem skew_double_sum_eq_zero {α : Type*} (B : α → α → ℝ)
    (hB : ∀ i j, B i j = -B j i) (E : Finset α) :
    (∑ i ∈ E, ∑ j ∈ E, B i j) = 0 := by
  have h : (∑ i ∈ E, ∑ j ∈ E, B i j) = -(∑ i ∈ E, ∑ j ∈ E, B i j) := by
    calc
      _ = ∑ j ∈ E, ∑ i ∈ E, B i j := Finset.sum_comm
      _ = ∑ j ∈ E, ∑ i ∈ E, -B j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact hB i j
      _ = _ := by simp
  linarith

theorem signed_skew_internal_le {α : Type*} (B : α → α → ℝ)
    (hB : ∀ i j, B i j = -B j i) (hentry : ∀ i j, |B i j| ≤ 1)
    (a : α → ℝ) (ha : ∀ i, a i = 1 ∨ a i = -1) (H : Finset α) :
    (∑ i ∈ H, ∑ j ∈ H, a i * B i j) ≤
      (H.card : ℝ) ^ 2 - (halfSquare H.card : ℝ) := by
  classical
  let P := H.filter (fun i => a i = 1)
  let Q := H.filter (fun i => a i ≠ 1)
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hi).2
  have hu : P ∪ Q = H := Finset.filter_union_filter_not_eq _ _
  have hp : ∀ i ∈ P, a i = 1 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hq : ∀ i ∈ Q, a i = -1 := by
    intro i hi
    exact (ha i).resolve_left (Finset.mem_filter.mp hi).2
  have hrow (i : α) : (∑ j ∈ H, B i j) =
      (∑ j ∈ P, B i j) + ∑ j ∈ Q, B i j := by
    rw [← Finset.sum_union hd, hu]
  have hqp : (∑ i ∈ Q, ∑ j ∈ P, B i j) = -(∑ i ∈ P, ∑ j ∈ Q, B i j) := by
    calc
      _ = ∑ j ∈ P, ∑ i ∈ Q, B i j := Finset.sum_comm
      _ = ∑ j ∈ P, ∑ i ∈ Q, -B j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact hB i j
      _ = _ := by simp
  have he : (∑ i ∈ H, ∑ j ∈ H, a i * B i j) =
      2 * (∑ i ∈ P, ∑ j ∈ Q, B i j) := by
    calc
      _ = (∑ i ∈ P, ∑ j ∈ H, a i * B i j) +
          ∑ i ∈ Q, ∑ j ∈ H, a i * B i j := by
        rw [← Finset.sum_union hd, hu]
      _ = (∑ i ∈ P, ∑ j ∈ H, B i j) - ∑ i ∈ Q, ∑ j ∈ H, B i j := by
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          simp [hp i hi]
        · rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          simp [hq i hi]
      _ = _ := by
        simp_rw [hrow, Finset.sum_add_distrib]
        rw [skew_double_sum_eq_zero B hB P, skew_double_sum_eq_zero B hB Q, hqp]
        ring
  have hc : (∑ i ∈ P, ∑ j ∈ Q, B i j) ≤ (P.card : ℝ) * Q.card := by
    calc
      _ ≤ ∑ i ∈ P, ∑ j ∈ Q, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact (le_abs_self _).trans (hentry i j)
      _ = _ := by simp
  have hcard : P.card + Q.card = H.card := by
    rw [← Finset.card_union_of_disjoint hd, hu]
  have hhNat : halfSquare H.card ≤ P.card * P.card + Q.card * Q.card := by
    rw [← hcard]
    exact halfSquare_le_sum_sq _ _
  have hh : (halfSquare H.card : ℝ) ≤
      (P.card : ℝ) * P.card + (Q.card : ℝ) * Q.card := by exact_mod_cast hhNat
  have hcardR : (P.card : ℝ) + Q.card = H.card := by exact_mod_cast hcard
  have hsquare : (H.card : ℝ) ^ 2 = ((P.card : ℝ) + Q.card) ^ 2 := by rw [hcardR]
  nlinarith

theorem signed_indicator_bilinear_le_inter {α : Type*} [DecidableEq α]
    (A : α → α → ℝ) (hskew : ∀ i j, A i j = -A j i)
    (hentry : ∀ i j, |A i j| ≤ 1) (S I : Finset α)
    (ε η : α → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hη : ∀ i, η i = 1 ∨ η i = -1) :
    (∑ i ∈ S, ∑ j ∈ I, ε i * A i j * η j) ≤
      (S.card : ℝ) * I.card - (halfSquare (S ∩ I).card : ℝ) := by
  classical
  let H := S ∩ I
  let B : α → α → ℝ := fun i j => η i * A i j * η j
  let a : α → ℝ := fun i => ε i * η i
  have hηsq (i : α) : η i * η i = 1 := by
    rcases hη i with h | h <;> simp [h]
  have hεabs (i : α) : |ε i| = 1 := by
    rcases hε i with h | h <;> simp [h]
  have hηabs (i : α) : |η i| = 1 := by
    rcases hη i with h | h <;> simp [h]
  have ha (i : α) : a i = 1 ∨ a i = -1 := by
    rcases hε i with hi | hi <;> rcases hη i with hj | hj <;> simp [a, hi, hj]
  have hB (i j : α) : B i j = -B j i := by
    dsimp [B]
    rw [hskew i j]
    ring
  have hBentry (i j : α) : |B i j| ≤ 1 := by
    simpa only [B, abs_mul, hηabs, one_mul, mul_one] using hentry i j
  have heterm (i j : α) : ε i * A i j * η j = a i * B i j := by
    dsimp [a, B]
    calc
      _ = ε i * (η i * η i) * A i j * η j := by rw [hηsq]; ring
      _ = _ := by ring
  let E := S ×ˢ I
  let D := H ×ˢ H
  let f : α × α → ℝ := fun p => ε p.1 * A p.1 p.2 * η p.2
  have hDE : D ⊆ E := by
    intro p hp
    simp only [D, E, H, Finset.mem_product, Finset.mem_inter] at hp ⊢
    exact ⟨hp.1.1, hp.2.2⟩
  have hf (p : α × α) : f p ≤ 1 := by
    calc
      _ ≤ |f p| := le_abs_self _
      _ = |A p.1 p.2| := by simp only [f, abs_mul, hεabs, hηabs, one_mul, mul_one]
      _ ≤ 1 := hentry _ _
  have hout : (∑ p ∈ E \ D, f p) ≤ ((E \ D).card : ℝ) := by
    calc
      _ ≤ ∑ p ∈ E \ D, (1 : ℝ) := Finset.sum_le_sum (fun p _ => hf p)
      _ = _ := by simp
  have hcount : ((E \ D).card : ℝ) = (S.card : ℝ) * I.card - (H.card : ℝ) ^ 2 := by
    rw [Finset.card_sdiff_of_subset hDE, Nat.cast_sub (Finset.card_le_card hDE)]
    simp only [E, D, Finset.card_product, Nat.cast_mul]
    ring
  have hinner : (∑ p ∈ D, f p) ≤ (H.card : ℝ) ^ 2 - (halfSquare H.card : ℝ) := by
    calc
      _ = ∑ i ∈ H, ∑ j ∈ H, a i * B i j := by
        simp only [D, Finset.sum_product, f, heterm]
      _ ≤ _ := signed_skew_internal_le B hB hBentry a ha H
  have hsum := Finset.sum_sdiff (f := f) hDE
  have he : (∑ p ∈ E, f p) = ∑ i ∈ S, ∑ j ∈ I, ε i * A i j * η j := by
    simp only [E, Finset.sum_product, f]
  rw [he] at hsum
  rw [hcount] at hout
  change _ ≤ (S.card : ℝ) * I.card - (halfSquare H.card : ℝ)
  linarith

/-- The dimension-uniform rectangle bound for arbitrary input and output signs. -/
theorem signed_indicator_bilinear_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) (hentry : ∀ i j, |A i j| ≤ 1)
    (S I : Finset (Fin n)) (ε η : Fin n → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hη : ∀ i, η i = 1 ∨ η i = -1) :
    (∑ i ∈ S, ∑ j ∈ I, ε i * A i j * η j) ≤ blockBudget n S.card I.card := by
  have h := signed_indicator_bilinear_le_inter A hskew hentry S I ε η hε hη
  have hu : (S ∪ I).card ≤ n := by simpa using (S ∪ I).card_le_univ
  have hcard := Finset.card_union_add_card_inter S I
  have hlow : S.card + I.card - n ≤ (S ∩ I).card := by omega
  have hh := halfSquare_mono hlow
  have hhR : (halfSquare (S.card + I.card - n) : ℝ) ≤ halfSquare (S ∩ I).card := by
    exact_mod_cast hh
  unfold blockBudget
  linarith

/-- The sharp finite support bound, valid for every selected output set. -/
theorem signed_indicator_abs_sum_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hskew : ∀ i j, A i j = -A j i) (hentry : ∀ i j, |A i j| ≤ 1)
    (S I : Finset (Fin n)) (η : Fin n → ℝ)
    (hη : ∀ i, η i = 1 ∨ η i = -1) :
    (∑ i ∈ S, |∑ j ∈ I, A i j * η j|) ≤ blockBudget n S.card I.card := by
  classical
  let ε : Fin n → ℝ := fun i => if 0 ≤ ∑ j ∈ I, A i j * η j then 1 else -1
  have hε (i : Fin n) : ε i = 1 ∨ ε i = -1 := by
    dsimp [ε]
    split_ifs <;> simp
  have he (i : Fin n) : ε i * (∑ j ∈ I, A i j * η j) = |∑ j ∈ I, A i j * η j| := by
    by_cases h : 0 ≤ ∑ j ∈ I, A i j * η j
    · simp [ε, h, abs_of_nonneg h]
    · simp [ε, h, abs_of_neg (lt_of_not_ge h)]
  have hrow (i : Fin n) : (∑ j ∈ I, ε i * A i j * η j) =
      ε i * (∑ j ∈ I, A i j * η j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [hrow, he] using signed_indicator_bilinear_le A hskew hentry S I ε η hε hη

end TournamentHamiltonian
