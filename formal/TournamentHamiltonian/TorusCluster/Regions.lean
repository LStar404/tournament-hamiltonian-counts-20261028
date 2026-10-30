module

public import TournamentHamiltonian.TorusCluster.Circle
public import TournamentHamiltonian.TorusCluster.Graph

@[expose] public section

set_option autoImplicit false
namespace TorusCluster
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

/-- Actual closed arc vertex set for the fixed center c. -/
def arc (x : Fin m → ℝ) (c a : ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => circleDist (x i) c ≤ a

def core (x : Fin m → ℝ) (c : ℝ) := arc x c (Real.pi/32)
def inner (x : Fin m → ℝ) (c : ℝ) := arc x c (Real.pi/8)
def outer (x : Fin m → ℝ) (c : ℝ) := arc x c (3*Real.pi/16)
def far (x : Fin m → ℝ) (c : ℝ) := (inner x c)ᶜ
def outliers (x : Fin m → ℝ) (c : ℝ) := (outer x c)ᶜ

@[simp] lemma mem_arc (x : Fin m → ℝ) (c a : ℝ) (i : Fin m) :
    i ∈ arc x c a ↔ circleDist (x i) c ≤ a := by simp [arc]
lemma arc_mono (x : Fin m → ℝ) (c : ℝ) {a b : ℝ} (h : a ≤ b) :
    arc x c a ⊆ arc x c b := by
  intro i hi
  exact (mem_arc _ _ _ _).mpr ((mem_arc _ _ _ _).mp hi |>.trans h)
lemma core_subset_inner (x : Fin m → ℝ) (c : ℝ) : core x c ⊆ inner x c := by
  apply arc_mono; linarith [Real.pi_pos]
lemma inner_subset_outer (x : Fin m → ℝ) (c : ℝ) : inner x c ⊆ outer x c := by
  apply arc_mono; linarith [Real.pi_pos]
lemma far_core_disjoint (x : Fin m → ℝ) (c : ℝ) : Disjoint (far x c) (core x c) := by
  exact Finset.disjoint_left.mpr fun _ hi hc => (Finset.mem_compl.mp hi) (core_subset_inner x c hc)
lemma outliers_outer_disjoint (x : Fin m → ℝ) (c : ℝ) : Disjoint (outliers x c) (outer x c) :=
  disjoint_compl_left
lemma outliers_inner_disjoint (x : Fin m → ℝ) (c : ℝ) : Disjoint (outliers x c) (inner x c) := by
  exact Finset.disjoint_left.mpr fun _ hi hc => (Finset.mem_compl.mp hi) (inner_subset_outer x c hc)

lemma inner_card_add_far_card (x : Fin m → ℝ) (c : ℝ) :
    (inner x c).card + (far x c).card = m := by
  simp [far]
lemma outer_card_add_outliers_card (x : Fin m → ℝ) (c : ℝ) :
    (outer x c).card + (outliers x c).card = m := by
  simp [outliers]

/-- Pigeonhole uses the proved cover of the actual configuration, not a supplied cardinal bound. -/
theorem exists_large_core (x : Fin m → ℝ) :
    ∃ j : Fin 16, (m : ℝ)/16 ≤ (core x (center j)).card := by
  have hsum : (m : ℝ) ≤ ∑ j : Fin 16, ((core x (center j)).card : ℝ) := by
    have hp (i : Fin m) : (1 : ℝ) ≤ ∑ j : Fin 16,
        if circleDist (x i) (center j) ≤ Real.pi/32 then 1 else 0 := by
      obtain ⟨j,hj⟩ := sixteen_arc_cover (x i)
      calc
        (1 : ℝ) = (if circleDist (x i) (center j) ≤ Real.pi/32 then 1 else 0) := by simp [hj]
        _ ≤ ∑ j : Fin 16, if circleDist (x i) (center j) ≤ Real.pi/32 then 1 else 0 := by
          apply Finset.single_le_sum (f := fun j : Fin 16 =>
            if circleDist (x i) (center j) ≤ Real.pi/32 then (1 : ℝ) else 0)
          · intro k _; split_ifs <;> norm_num
          · exact Finset.mem_univ j
    calc
      (m : ℝ) = ∑ _i : Fin m, (1 : ℝ) := by simp
      _ ≤ ∑ i : Fin m, ∑ j : Fin 16,
          if circleDist (x i) (center j) ≤ Real.pi/32 then (1 : ℝ) else 0 :=
        Finset.sum_le_sum (fun i _ => hp i)
      _ = ∑ j : Fin 16, ((core x (center j)).card : ℝ) := by
        rw [Finset.sum_comm]
        simp only [core, arc, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
          Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  by_contra hn
  push Not at hn
  have hl := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 16)))
    Finset.univ_nonempty (fun j _ => hn j)
  have he : (∑ _j : Fin 16, (m : ℝ)/16) = m := by simp; ring
  linarith

lemma far_core_separated (x : Fin m → ℝ) (c : ℝ) {i j : Fin m}
    (hi : i ∈ far x c) (hj : j ∈ core x c) :
    3*Real.pi/32 ≤ circleDist (x i) (x j) := by
  have hi' : Real.pi/8 < circleDist (x i) c := by simpa [far, inner] using hi
  have hj' : circleDist (x j) c ≤ Real.pi/32 := by simpa [core] using hj
  have ht := circleDist_triangle (x i) (x j) c
  linarith

lemma outlier_inner_separated (x : Fin m → ℝ) (c : ℝ) {i j : Fin m}
    (hi : i ∈ outliers x c) (hj : j ∈ inner x c) :
    Real.pi/16 ≤ circleDist (x i) (x j) := by
  have hi' : 3*Real.pi/16 < circleDist (x i) c := by simpa [outliers, outer] using hi
  have hj' : circleDist (x j) c ≤ Real.pi/8 := by simpa [inner] using hj
  have ht := circleDist_triangle (x i) (x j) c
  linarith

lemma inner_large_of_not_far (x : Fin m → ℝ) (c : ℝ)
    (hf : ((far x c).card : ℝ) < (m : ℝ)/4) :
    3*(m : ℝ)/4 < (inner x c).card := by
  have h := inner_card_add_far_card x c
  have h' : ((inner x c).card : ℝ) + (far x c).card = m := by exact_mod_cast h
  linarith

lemma outliers_lt_quarter_of_not_far (x : Fin m → ℝ) (c : ℝ)
    (hf : ((far x c).card : ℝ) < (m : ℝ)/4) :
    ((outliers x c).card : ℝ) < (m : ℝ)/4 := by
  have hs : outliers x c ⊆ far x c := by
    exact Finset.compl_subset_compl.mpr (inner_subset_outer x c)
  have hc : ((outliers x c).card : ℝ) ≤ (far x c).card := by
    exact_mod_cast Finset.card_le_card hs
  exact hc.trans_lt hf

/-- Exhaustive three-region cover; no measurable or configuration-dependent selection is asserted. -/
theorem three_region_cover (x : Fin m → ℝ) :
    ∃ j : Fin 16, (m : ℝ)/16 ≤ (core x (center j)).card ∧
      ((m : ℝ)/4 ≤ (far x (center j)).card ∨
        (((far x (center j)).card : ℝ) < (m : ℝ)/4 ∧
          0 < (outliers x (center j)).card) ∨
        (outliers x (center j)).card = 0) := by
  obtain ⟨j,hj⟩ := exists_large_core x
  refine ⟨j,hj,?_⟩
  by_cases hf : (m : ℝ)/4 ≤ (far x (center j)).card
  · exact Or.inl hf
  · by_cases ho : (outliers x (center j)).card = 0
    · exact Or.inr (Or.inr ho)
    · exact Or.inr (Or.inl ⟨lt_of_not_ge hf, Nat.pos_of_ne_zero ho⟩)

end
end TorusCluster
