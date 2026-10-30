module

public import TournamentHamiltonian.NonregularNormalization.Targets
public import TournamentHamiltonian.NonregularDecay.CycleBound

@[expose] public section

set_option autoImplicit false
namespace NonregularNormalization
open TournamentHamiltonian RegularOrientation UniformBlowup NonregularKappa
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The exact grouped Brégman exponential, before any normalization. -/
def blockBregman {d : ℕ} (R : Fin d → ℕ) (m : ℕ) : ℝ :=
  Real.exp ((m : ℝ) * ∑ i, Real.log ((R i).factorial : ℝ) / R i)

/-- One row's fine Stirling remainder with the manuscript constants. -/
theorem row_log_factorial_bound {m N R : ℕ} (hm : 2 ≤ m) (hR : 1 ≤ R)
    (hlow : (m : ℝ)/4 ≤ R) (hRN : R ≤ N) :
    (m : ℝ)* (Real.log (R.factorial : ℝ)/R) ≤
      (m : ℝ)*Real.log R-m+2*Real.log (2*Real.pi*N)+4/(3*(m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hRN' : (R : ℝ) ≤ N := by exact_mod_cast hRN
  have hlog := Real.log_le_log (by positivity : 0 < 2*Real.pi*(R : ℝ))
    (mul_le_mul_of_nonneg_left hRN' (by positivity : 0 ≤ 2*Real.pi))
  have hlogN : 0 ≤ Real.log (2*Real.pi*(N : ℝ)) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hcoef : (m : ℝ)/(2*R) ≤ 2 := by apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hrem1 : (m : ℝ)/(2*R)*Real.log (2*Real.pi*R) ≤ 2*Real.log (2*Real.pi*N) := by
    exact (mul_le_mul_of_nonneg_left hlog (by positivity)).trans
      (mul_le_mul_of_nonneg_right hcoef hlogN)
  have hsq : (m : ℝ)^2 ≤ 16*(R : ℝ)^2 := by
    have hh := mul_self_le_mul_self hm0.le (show (m : ℝ) ≤ 4*R by linarith)
    nlinarith
  have hrem2 : (m : ℝ)/(12*(R : ℝ)^2) ≤ 4/(3*(m : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have h := mul_le_mul_of_nonneg_left (log_factorial_robbins_upper R hR)
    (show 0 ≤ (m : ℝ)/R by positivity)
  have he : (m : ℝ)/R * ((R : ℝ)*Real.log R-R+Real.log (2*Real.pi*R)/2+1/(12*(R : ℝ))) =
      (m : ℝ)*Real.log R-m + (m : ℝ)/(2*R)*Real.log (2*Real.pi*R) +
        (m : ℝ)/(12*(R : ℝ)^2) := by field_simp
  rw [he] at h
  have hl : (m : ℝ)/R*Real.log (R.factorial : ℝ) = (m : ℝ)*(Real.log (R.factorial : ℝ)/R) := by ring
  rw [hl] at h
  linarith

theorem log_factorial_normalization_lower {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)*Real.log ((N : ℝ)/2)-N ≤ Real.log ((N.factorial : ℝ)/(2 : ℝ)^N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (2*Real.pi*(N : ℝ)) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have h := log_factorial_stirling_lower N hN
  have hnlog : Real.log ((N.factorial : ℝ)/(2 : ℝ)^N) = Real.log (N.factorial : ℝ) - (N : ℝ)*Real.log 2 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  rw [hnlog, Real.log_div hN0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  linarith

/-- Rounding changes the scaled leading log by at most 2 per base vertex.
Only an upper logarithmic estimate is needed; no absolute-log Taylor bound is assumed. -/
theorem row_log_ratio_bound {d m R : ℕ} (hd : 0 < d) (hm : 2 ≤ m)
    (T : Tournament d) (i : Fin d) (hR : 1 ≤ R)
    (hup : (R : ℝ) ≤ (m : ℝ)*baseB T i+1/2) :
    (m : ℝ)*Real.log (2*(R : ℝ)/(d*m)) ≤
      (m : ℝ)*Real.log (degreeParameter T i)+2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hb := (baseB_bounds hd T i).1
  have hb0 : 0 < baseB T i := by linarith
  have hx0 : 0 < (R : ℝ)/((m : ℝ)*baseB T i) := by positivity
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx0) hm0.le
  have he : (m : ℝ)*((R : ℝ)/((m : ℝ)*baseB T i)-1) = ((R : ℝ)-(m : ℝ)*baseB T i)/baseB T i := by
    field_simp
  rw [he] at hlog
  have hfrac : ((R : ℝ)-(m : ℝ)*baseB T i)/baseB T i ≤ 2 := by
    apply (div_le_iff₀ hb0).mpr
    linarith
  have heq : 2*(R : ℝ)/(d*m) = degreeParameter T i * ((R : ℝ)/((m : ℝ)*baseB T i)) := by
    rw [degreeParameter_eq_baseB hd]
    field_simp
  rw [heq, Real.log_mul (degreeParameter_pos hd T i).ne' hx0.ne']
  nlinarith

/-- The entire logarithmic normalization with the manuscript constant 8d/3. -/
theorem target_log_sum_bound {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (T : Tournament d) :
    (m : ℝ)* (∑ i, Real.log ((rowTarget T m i).factorial : ℝ) / rowTarget T m i) ≤
      Real.log (((d*m).factorial : ℝ)/(2 : ℝ)^(d*m)) +
        (d*m : ℝ)*Real.log (kappa T) + 8*(d : ℝ)/3 +
        2*(d : ℝ)*Real.log (2*Real.pi*(d*m)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hN0 : (0 : ℝ) < (d*m : ℝ) := by positivity
  have hN : 1 ≤ d*m := Nat.succ_le_of_lt (Nat.mul_pos hd (by omega))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ =>
    row_log_factorial_bound hm (rowTarget_spec hd hm T i).1
      (rowTarget_spec hd hm T i).2.2.1 (rowTarget_spec hd hm T i).2.1)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul] at hs
  have hr := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ =>
    row_log_ratio_bound hd hm T i (rowTarget_spec hd hm T i).1
      (rowTarget_spec hd hm T i).2.2.2.2.le)
  have he (i : Fin d) : Real.log (2*(rowTarget T m i : ℝ)/(d*m)) =
      Real.log (rowTarget T m i) - Real.log ((d*m : ℝ)/2) := by
    have hRi : (0 : ℝ) < rowTarget T m i := by exact_mod_cast (show 0 < rowTarget T m i by have := (rowTarget_spec hd hm T i).1; omega)
    rw [Real.log_div (by positivity) hN0.ne',
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRi.ne',
      Real.log_div hN0.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  simp_rw [he] at hr
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hr
  have hk : (m : ℝ)*(∑ i, Real.log (degreeParameter T i)) = (d*m : ℝ)*Real.log (kappa T) := by
    rw [log_kappa]
    field_simp
  rw [hk] at hr
  have hl := log_factorial_normalization_lower hN
  simp only [Nat.cast_mul] at hl
  have hrem : (d : ℝ)*(4/(3*(m : ℝ))) ≤ 2*(d : ℝ)/3 := by
    have hh : (4 : ℝ)/(3*(m : ℝ)) ≤ 2/3 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hh hd0.le]
  nlinarith

/-- The precise cycle-scale Brégman majorant printed in §11.5, before any
sample/model specialization. -/
theorem blockBregman_cycle_rate {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (T : Tournament d) :
    blockBregman (rowTarget T m) m / NonregularDecay.meanCycles (d*m) ≤
      Real.exp (8*(d : ℝ)/3) * (2*Real.pi)^(2*d) *
        (d*m : ℝ)^(2*d+1) * kappa T^(d*m) := by
  have hN : 1 ≤ d*m := Nat.succ_le_of_lt (Nat.mul_pos hd (by omega))
  have hN0 : (0 : ℝ) < (d*m : ℝ) := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    positivity
  have he := Real.exp_le_exp.mpr (target_log_sum_bound hd hm T)
  have hk : Real.exp ((d*m : ℝ)*Real.log (kappa T)) = kappa T^(d*m) := by
    rw [show (d*m : ℝ) = ((d*m : ℕ) : ℝ) by push_cast; rfl,
      Real.exp_nat_mul, Real.exp_log (kappa_pos T)]
  have hp : Real.exp (2*(d : ℝ)*Real.log (2*Real.pi*(d*m))) = (2*Real.pi*(d*m : ℝ))^(2*d) := by
    rw [show 2*(d : ℝ) = ((2*d : ℕ) : ℝ) by push_cast; rfl,
      Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log (by positivity), hk, hp] at he
  apply (div_le_iff₀ (NonregularDecay.meanCycles_pos _)).mpr
  calc
    blockBregman (rowTarget T m) m ≤ _ := he
    _ = _ := by
      rw [NonregularDecay.factorial_normalization_eq _ hN, mul_pow, pow_succ]
      push_cast
      ring

end
end NonregularNormalization
