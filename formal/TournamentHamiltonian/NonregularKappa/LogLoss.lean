module

public import TournamentHamiltonian.NonregularDecay.Variance

@[expose] public section

set_option autoImplicit false
namespace NonregularKappa
open TournamentHamiltonian RegularOrientation
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The quantitative scalar logarithm loss required by manuscript §11.3.
A square-root substitution avoids any imported Taylor-remainder hypothesis. -/
theorem log_le_sub_one_sub_sq {a : ℝ} (ha : 0 < a) (ha2 : a < 2) :
    Real.log a ≤ a-1-(a-1)^2/8 := by
  have hs0 : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hs : (Real.sqrt a)^2 = a := Real.sq_sqrt ha.le
  have hlog := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ha)
  rw [Real.log_sqrt ha.le] at hlog
  have hs15 : Real.sqrt a ≤ 3/2 := by nlinarith
  have hb : (Real.sqrt a+1)^2 ≤ 8 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg (Real.sqrt a-1))
  have he : (Real.sqrt a-1)^2*(Real.sqrt a+1)^2 = (a-1)^2 := by nlinarith [sq_nonneg (Real.sqrt a)]
  rw [he] at hm
  nlinarith

/-- The manuscript's a_i, using its existing signed-score convention. -/
def degreeParameter {d : ℕ} (T : Tournament d) (i : Fin d) : ℝ :=
  1 + score T i / d

/-- The same a_i expressed with the actual natural outdegree. -/
theorem degreeParameter_eq_outDegree {d : ℕ} (hd : 0 < d) (T : Tournament d) (i : Fin d) :
    degreeParameter T i = (2 * (outDegree T i : ℝ) + 1) / d := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  rw [degreeParameter, score_eq_outDegree]
  field_simp
  ring

theorem degreeParameter_pos {d : ℕ} (hd : 0 < d) (T : Tournament d) (i : Fin d) :
    0 < degreeParameter T i := by
  rw [degreeParameter_eq_outDegree hd]
  positivity

theorem outDegree_le_order_pred {d : ℕ} (T : Tournament d) (i : Fin d) :
    outDegree T i ≤ d-1 := by
  exact TournamentHamiltonian.rowDegree_le_order_pred T i

theorem degreeParameter_lt_two {d : ℕ} (hd : 0 < d) (T : Tournament d) (i : Fin d) :
    degreeParameter T i < 2 := by
  rw [degreeParameter_eq_outDegree hd]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_lt_iff₀ hdR).mpr
  have h := outDegree_le_order_pred T i
  have hR : (outDegree T i : ℝ) ≤ (d : ℝ)-1 := by
    have hr : (outDegree T i : ℝ) ≤ ((d-1 : ℕ) : ℝ) := by exact_mod_cast h
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using hr
  linarith

theorem degreeParameter_sum {d : ℕ} (T : Tournament d) :
    ∑ i, degreeParameter T i = d := by
  simp [degreeParameter, Finset.sum_add_distrib, ← Finset.sum_div, score_sum_zero]

/-- The actual geometric-mean factor, with its positive exponential definition. -/
def kappa {d : ℕ} (T : Tournament d) : ℝ :=
  Real.exp ((∑ i, Real.log (degreeParameter T i)) / d)

theorem kappa_pos {d : ℕ} (T : Tournament d) : 0 < kappa T := Real.exp_pos _

theorem log_kappa {d : ℕ} (T : Tournament d) :
    Real.log (kappa T) = (∑ i, Real.log (degreeParameter T i)) / d :=
  Real.log_exp _

theorem kappa_eq_geometricMean {d : ℕ} (hd : 0 < d) (T : Tournament d) :
    kappa T = (∏ i, degreeParameter T i) ^ ((1 : ℝ) / d) := by
  have hp : 0 < ∏ i, degreeParameter T i := Finset.prod_pos fun i _ => degreeParameter_pos hd T i
  rw [Real.rpow_def_of_pos hp]
  rw [Real.log_prod (fun i _ => (degreeParameter_pos hd T i).ne')]
  simp [kappa, div_eq_mul_inv]

/-- Quantitative score penalty, retaining the manuscript's factor 1/(8*d^3). -/
theorem log_kappa_le_score_loss {d : ℕ} (hd : 0 < d) (T : Tournament d) :
    Real.log (kappa T) ≤ -(∑ i, score T i^2) / (8*(d : ℝ)^3) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    log_le_sub_one_sub_sq (degreeParameter_pos hd T i) (degreeParameter_lt_two hd T i))
  have he (i : Fin d) : degreeParameter T i-1-(degreeParameter T i-1)^2/8 =
      score T i / d - score T i^2 / (8*(d : ℝ)^2) := by
    rw [degreeParameter]
    field_simp
    ring
  simp_rw [he] at h
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, score_sum_zero, zero_div, zero_sub] at h
  rw [log_kappa]
  have hh := div_le_div_of_nonneg_right h hdR.le
  convert hh using 1
  field_simp

theorem kappa_lt_one_of_nonregular {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬IsRegular T) : kappa T < 1 := by
  have hV := (NonregularDecay.degreeVariance_pos_iff_nonregular T).mpr hT
  rw [degreeVariance_eq_score_sum] at hV
  have hs : 0 < ∑ i, score T i^2 := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : Real.log (kappa T) < 0 :=
    (log_kappa_le_score_loss hd T).trans_lt (div_neg_of_neg_of_pos (neg_neg_of_pos hs) (by positivity))
  exact (Real.log_neg_iff (kappa_pos T)).mp hlog

/-- Combined positivity/strict-loss statement for the actual nonregular base. -/
theorem kappa_bounds_nonregular {d : ℕ} (hd : 0 < d) (T : Tournament d)
    (hT : ¬RegularOrientation.IsRegular T) : 0 < kappa T ∧ kappa T < 1 :=
  ⟨kappa_pos T, kappa_lt_one_of_nonregular hd T hT⟩

/-- Boundary check: a genuinely regular base has every a_i=1 and κ=1. -/
theorem kappa_eq_one_of_regular {d : ℕ} (T : Tournament d)
    (hT : RegularOrientation.IsRegular T) : kappa T = 1 := by
  have hs : ∀ i, score T i = 0 := hT
  simp [kappa, degreeParameter, hs]

end
end NonregularKappa
