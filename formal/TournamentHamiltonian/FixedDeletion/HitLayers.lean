module

public import TournamentHamiltonian.FixedDeletion.Reindex
public import TournamentHamiltonian.FixedDeletion.Budget

@[expose] public section

set_option autoImplicit false
namespace FixedDeletion
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def layer (n j : ℕ) : Finset (Finset (Fin n)) := Finset.univ.powersetCard j

def hitLayer {n : ℕ} (U : Finset (Fin n)) (j : ℕ) : Finset (Finset (Fin n)) :=
  (layer n j).filter (fun V => ¬ Disjoint U V)

theorem hitLayer_zero {n : ℕ} (U : Finset (Fin n)) : hitLayer U 0 = ∅ := by
  simp [hitLayer, layer]

theorem hitLayer_card {n j : ℕ} (U : Finset (Fin n)) (hj : 1 ≤ j) :
    (hitLayer U j).card ≤ U.card * (n-1).choose (j-1) := by
  have hs : hitLayer U j ⊆ U.biUnion (fun i => (layer n j).filter (fun V => i ∈ V)) := by
    intro V hV
    obtain ⟨hV, hdis⟩ := Finset.mem_filter.mp hV
    have hx : ∃ i ∈ U, i ∈ V := Finset.not_disjoint_iff.mp hdis
    obtain ⟨i,hi,hiv⟩ := hx
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_filter.mpr ⟨hV,hiv⟩⟩
  apply (Finset.card_le_card hs).trans
  apply Finset.card_biUnion_le.trans
  have hc (i : Fin n) : ((layer n j).filter (fun V => i ∈ V)).card = (n-1).choose (j-1) := by
    simpa [layer, Finset.singleton_subset_iff] using
      Finset.card_filter_powersetCard_subset ({i} : Finset (Fin n)) Finset.univ j
        (Finset.subset_univ _) (by simpa using hj)
  simp [hc]

theorem hit_sum_le {n j : ℕ} (hn : 0 < n) (U : Finset (Fin n))
    (f : Finset (Fin n) → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hf : ∀ V ∈ layer n j, |f V| ≤ b) :
    (∑ V ∈ hitLayer U j, |f V|) ≤
      ((U.card : ℝ)*j/n)*((n.choose j : ℝ)*b) := by
  by_cases hj : j = 0
  · subst j; simp [hitLayer_zero]
  have hj1 : 1 ≤ j := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hchoose : (n.choose j : ℝ)*(j : ℝ) = (n : ℝ)*((n-1).choose (j-1) : ℝ) := by
    exact_mod_cast (show n.choose j*j = n*(n-1).choose (j-1) by
      simpa using (Nat.choose_mul (n := n) (k := j) (s := 1) hj1))
  calc
    _ ≤ ∑ _V ∈ hitLayer U j, b := Finset.sum_le_sum fun V hV => hf V (Finset.mem_filter.mp hV).1
    _ = ((hitLayer U j).card : ℝ)*b := by simp
    _ ≤ ((U.card * (n-1).choose (j-1) : ℕ) : ℝ)*b :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hitLayer_card U hj1) hb
    _ = _ := by push_cast; field_simp; nlinarith [congrArg (fun x : ℝ => (U.card : ℝ)*b*x) hchoose]

/-- A cardinal-times-pointwise bound, retaining the coefficient estimate used
in the original layer proof, so it may be applied to a restricted layer. -/
theorem cycle_card_point_bound {n : ℕ} (hn : 0 < n) (j : ℕ) :
    (n.choose j : ℝ) * ((j : ℝ)*(3/(n : ℝ))^j*Real.sqrt ((j : ℝ)^j)) ≤ denseCountWeight j := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ ≤ ((n : ℝ)^j/(j.factorial : ℝ))*((j : ℝ)*(3/(n : ℝ))^j*Real.sqrt ((j : ℝ)^j)) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div j n) (by positivity)
    _ = (j : ℝ)*3^j*denseHadamardWeight j := by
      unfold denseHadamardWeight
      rw [div_pow]
      field_simp
    _ ≤ _ := by
      unfold denseCountWeight
      have hw := denseHadamardWeight_nonneg j
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) j,
        mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) j) hw]

theorem path_card_point_bound {n : ℕ} (hn : 0 < n) (j : ℕ) :
    (n.choose j : ℝ) * (((3/(n : ℝ))^j*Real.sqrt ((j : ℝ)^j)+
      (j : ℝ)*(3/(n : ℝ))^(j-1)*Real.sqrt ((j : ℝ)^j))/(n : ℝ)) ≤ denseCountWeight j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hj : j = 0
  · subst j
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, pow_zero, Real.sqrt_one,
      mul_one, zero_mul, add_zero, denseCountWeight, denseHadamardWeight_zero]
    simpa using (div_le_one hnR).mpr hn1
  have hj1 : 1 ≤ j := by omega
  have hpow (x : ℝ) : x^j = x^(j-1)*x := by rw [← pow_succ, Nat.sub_add_cancel hj1]
  calc
    _ ≤ ((n : ℝ)^j/(j.factorial : ℝ))*
        (((3/(n : ℝ))^j*Real.sqrt ((j : ℝ)^j)+
          (j : ℝ)*(3/(n : ℝ))^(j-1)*Real.sqrt ((j : ℝ)^j))/(n : ℝ)) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div j n) (by positivity)
    _ = ((1/(n : ℝ))+(j : ℝ)/3)*3^j*denseHadamardWeight j := by
      unfold denseHadamardWeight
      simp only [div_pow]
      rw [hpow (n : ℝ), hpow 3]
      field_simp
    _ ≤ _ := by
      unfold denseCountWeight
      apply mul_le_mul_of_nonneg_right _ (denseHadamardWeight_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hfirst : (1 : ℝ)/n ≤ 1 := (div_le_one hnR).mpr hn1
      have hsecond : (j : ℝ)/3 ≤ j := by nlinarith [Nat.cast_nonneg (α := ℝ) j]
      linarith

theorem cycle_hit_layer {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) (U : Finset (Fin n)) (j : ℕ) :
    (∑ V ∈ hitLayer U j, |cycleCoeff D V|) ≤ ((U.card : ℝ)*j/n)*denseCountWeight j := by
  have h := hit_sum_le hn U (cycleCoeff D) ((j : ℝ)*(3/(n : ℝ))^j*Real.sqrt ((j : ℝ)^j)) (by positivity) (by
    intro V hV
    have hc : V.card = j := (Finset.mem_powersetCard.mp hV).2
    simp only [cycleCoeff, abs_mul, abs_neg, Nat.abs_cast]
    rw [← hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hD.cycle_minor_hadamard V) (Nat.cast_nonneg (α := ℝ) V.card))
  exact h.trans (mul_le_mul_of_nonneg_left (cycle_card_point_bound hn j) (by positivity))

theorem path_hit_layer {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : DenseStochastic D) (hn : 0 < n) (U : Finset (Fin n)) (j : ℕ) :
    (∑ V ∈ hitLayer U j, |pathCoeff D V|/(n : ℝ)) ≤ ((U.card : ℝ)*j/n)*denseCountWeight j := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := hit_sum_le hn U (fun V => pathCoeff D V/(n : ℝ))
    (((3/(n : ℝ))^j*Real.sqrt ((j : ℝ)^j)+
      (j : ℝ)*(3/(n : ℝ))^(j-1)*Real.sqrt ((j : ℝ)^j))/(n : ℝ)) (by positivity) (by
      intro V hV
      have hc : V.card = j := (Finset.mem_powersetCard.mp hV).2
      rw [abs_div, abs_of_pos hnR, ← hc]
      exact div_le_div_of_nonneg_right (hD.path_minor_hadamard V) hnR.le)
  simp only [abs_div, abs_of_pos hnR] at h
  exact h.trans (mul_le_mul_of_nonneg_left (path_card_point_bound hn j) (by positivity))

end
end FixedDeletion
