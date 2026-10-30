module

public import TournamentHamiltonian.NonregularNormalization.FineStirling
public import TournamentHamiltonian.NonregularKappa.OddGap
public import TournamentHamiltonian.UniformBlowup.Marginal
public import TournamentHamiltonian.NonregularRate.WeightedBregman

@[expose] public section

set_option autoImplicit false
namespace NonregularNormalization
open TournamentHamiltonian RegularOrientation UniformBlowup NonregularKappa
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def baseB {d : ℕ} (T : Tournament d) (i : Fin d) : ℝ := outDegree T i + 1/2

theorem baseB_bounds {d : ℕ} (hd : 0 < d) (T : Tournament d) (i : Fin d) :
    1/2 ≤ baseB T i ∧ baseB T i ≤ (d : ℝ)-1/2 := by
  have h := NonregularKappa.outDegree_le_order_pred T i
  have hR : (outDegree T i : ℝ) ≤ (d : ℝ)-1 := by
    have hh : (outDegree T i : ℝ) ≤ ((d-1 : ℕ) : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using hh
  dsimp [baseB]
  constructor
  · have h0 : (0 : ℝ) ≤ outDegree T i := Nat.cast_nonneg _
    linarith
  · linarith

theorem degreeParameter_eq_baseB {d : ℕ} (hd : 0 < d) (T : Tournament d) (i : Fin d) :
    degreeParameter T i = 2*baseB T i/d := by
  rw [degreeParameter_eq_outDegree hd, baseB]
  ring

/-- The actual integral row target R_i=ceil(m b_i-1/2), rounded upwards. -/
def rowTarget {d : ℕ} (T : Tournament d) (m : ℕ) (i : Fin d) : ℕ :=
  ⌈(m : ℝ)*baseB T i-1/2⌉₊

theorem rowTarget_spec {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (T : Tournament d) (i : Fin d) :
    1 ≤ rowTarget T m i ∧ rowTarget T m i ≤ d*m ∧
    (m : ℝ)/4 ≤ rowTarget T m i ∧
    (m : ℝ)*baseB T i-1/2 ≤ rowTarget T m i ∧
    (rowTarget T m i : ℝ) < (m : ℝ)*baseB T i+1/2 := by
  obtain ⟨hb0,hbd⟩ := baseB_bounds hd T i
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < (m : ℝ)*baseB T i-1/2 := by nlinarith
  have hlo := Nat.le_ceil ((m : ℝ)*baseB T i-1/2)
  have hhi := Nat.ceil_lt_add_one hpos.le
  change (m : ℝ)*baseB T i-1/2 ≤ (rowTarget T m i : ℝ) at hlo
  change (rowTarget T m i : ℝ) < (m : ℝ)*baseB T i-1/2+1 at hhi
  refine ⟨?_, ?_, ?_, hlo, by linarith⟩
  · exact Nat.ceil_pos.mpr hpos
  · apply Nat.ceil_le.mpr
    push_cast
    nlinarith
  · nlinarith

/-- Exact actual expected-adjacency row sum; no expectation-factorization is used. -/
theorem uniform_weight_row_sum {d m : ℕ} (T : Tournament d) (u : Vertex d m) :
    ∑ v : Vertex d m, weight T u v = (m : ℝ)*baseB T u.1-1/2 := by
  simp_rw [weight_eq_block_formula]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hs : (∑ v : Vertex d m, signMatrix T u.1 v.1) = (m : ℝ)*score T u.1 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, score]
  rw [hs, score_eq_outDegree, baseB]
  push_cast
  ring

theorem uniform_weight_box {d m : ℕ} (T : Tournament d) (u v : Vertex d m) :
    0 ≤ weight T u v ∧ weight T u v ≤ 1 := by
  unfold weight
  split_ifs <;> norm_num

end
end NonregularNormalization
