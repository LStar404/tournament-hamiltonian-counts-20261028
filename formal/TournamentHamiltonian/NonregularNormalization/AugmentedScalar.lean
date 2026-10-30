module

public import TournamentHamiltonian.NonregularNormalization.AugmentedPath

@[expose] public section

set_option autoImplicit false
namespace NonregularNormalization
open TournamentHamiltonian RegularOrientation UniformBlowup NonregularKappa NonregularRate NonregularDecay
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def augRowTarget {d : ℕ} (T : Tournament d) (m : ℕ) (i : Fin d) : ℕ :=
  ⌈(m : ℝ)*baseB T i+1/2⌉₊

theorem augRowTarget_spec {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (T : Tournament d) (i : Fin d) :
    1 ≤ augRowTarget T m i ∧ augRowTarget T m i ≤ d*m ∧
    (m : ℝ)/4 ≤ augRowTarget T m i ∧
    (m : ℝ)*baseB T i ≤ augRowTarget T m i ∧
    (augRowTarget T m i : ℝ) < (m : ℝ)*baseB T i+3/2 := by
  obtain ⟨hb0,hbd⟩ := baseB_bounds hd T i
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : 0 < (m : ℝ)*baseB T i+1/2 := by nlinarith
  have hlo := Nat.le_ceil ((m : ℝ)*baseB T i+1/2)
  have hhi := Nat.ceil_lt_add_one hpos.le
  change (m : ℝ)*baseB T i+1/2 ≤ (augRowTarget T m i : ℝ) at hlo
  change (augRowTarget T m i : ℝ) < (m : ℝ)*baseB T i+1/2+1 at hhi
  refine ⟨Nat.ceil_pos.mpr hpos, ?_, by nlinarith, by linarith, by linarith⟩
  apply Nat.ceil_le.mpr
  push_cast
  nlinarith

def augBlockBregman {d : ℕ} (T : Tournament d) (m : ℕ) : ℝ :=
  Real.exp ((m : ℝ)*(∑ i, Real.log ((augRowTarget T m i).factorial : ℝ)/augRowTarget T m i) +
    Real.log (((d*m).factorial) : ℝ)/(d*m))

theorem aug_row_log_ratio_bound {d m R : ℕ} (hd : 0 < d) (hm : 2 ≤ m)
    (T : Tournament d) (i : Fin d) (hR : 1 ≤ R)
    (hup : (R : ℝ) ≤ (m : ℝ)*baseB T i+3/2) :
    (m : ℝ)*Real.log (2*(R : ℝ)/(d*m)) ≤ (m : ℝ)*Real.log (degreeParameter T i)+3 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hb := (baseB_bounds hd T i).1
  have hb0 : 0 < baseB T i := by linarith
  have hx0 : 0 < (R : ℝ)/((m : ℝ)*baseB T i) := by positivity
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hx0) hm0.le
  have he : (m : ℝ)*((R : ℝ)/((m : ℝ)*baseB T i)-1) = ((R : ℝ)-(m : ℝ)*baseB T i)/baseB T i := by field_simp
  rw [he] at hlog
  have hfrac : ((R : ℝ)-(m : ℝ)*baseB T i)/baseB T i ≤ 3 := by
    apply (div_le_iff₀ hb0).mpr
    linarith
  have heq : 2*(R : ℝ)/(d*m) = degreeParameter T i * ((R : ℝ)/((m : ℝ)*baseB T i)) := by
    rw [degreeParameter_eq_baseB hd]
    field_simp
  rw [heq, Real.log_mul (degreeParameter_pos hd T i).ne' hx0.ne']
  nlinarith

theorem new_row_log_factorial_bound {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N.factorial : ℝ)/N ≤
      Real.log N-1+Real.log (2*Real.pi*((N : ℝ)+1))+1/12 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log (2*Real.pi*(N : ℝ)) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlog := Real.log_le_log (by positivity : 0 < 2*Real.pi*(N : ℝ))
    (show 2*Real.pi*(N : ℝ) ≤ 2*Real.pi*((N : ℝ)+1) by nlinarith [Real.pi_pos])
  have hr1 : Real.log (2*Real.pi*(N : ℝ))/(2*N) ≤ Real.log (2*Real.pi*((N : ℝ)+1)) := by
    exact (div_le_self hlog0 (by linarith : (1 : ℝ) ≤ 2*N)).trans hlog
  have hr2 : (1 : ℝ)/(12*(N : ℝ)^2) ≤ 1/12 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  have h := div_le_div_of_nonneg_right (log_factorial_robbins_upper N hN) hN0.le
  have he : ((N : ℝ)*Real.log N-N+Real.log (2*Real.pi*N)/2+1/(12*(N : ℝ)))/N =
      Real.log N-1+Real.log (2*Real.pi*N)/(2*N)+1/(12*(N : ℝ)^2) := by field_simp
  rw [he] at h
  linarith

theorem augmented_log_sum_bound {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (T : Tournament d) :
    (m : ℝ)*(∑ i, Real.log ((augRowTarget T m i).factorial : ℝ)/augRowTarget T m i) +
        Real.log (((d*m).factorial) : ℝ)/(d*m) ≤
      Real.log (((d*m+1).factorial : ℝ)/(2 : ℝ)^(d*m+1)) +
        (d*m : ℝ)*Real.log (kappa T) + (11*(d : ℝ)/3+1/12) + Real.log 2 +
        (2*(d : ℝ)+1)*Real.log (2*Real.pi*((d*m : ℝ)+1)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hN0 : (0 : ℝ) < (d*m : ℝ) := by positivity
  have hN : 1 ≤ d*m := Nat.succ_le_of_lt (Nat.mul_pos hd (by omega))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ =>
    row_log_factorial_bound (N := d*m+1) hm (augRowTarget_spec hd hm T i).1
      (augRowTarget_spec hd hm T i).2.2.1 ((augRowTarget_spec hd hm T i).2.1.trans (Nat.le_succ _)))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hs
  have hr := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ =>
    aug_row_log_ratio_bound hd hm T i (augRowTarget_spec hd hm T i).1
      (augRowTarget_spec hd hm T i).2.2.2.2.le)
  have he (i : Fin d) : Real.log (2*(augRowTarget T m i : ℝ)/(d*m)) =
      Real.log (augRowTarget T m i) - Real.log ((d*m : ℝ)/2) := by
    have hRi : (0 : ℝ) < augRowTarget T m i := by exact_mod_cast (show 0 < augRowTarget T m i by have := (augRowTarget_spec hd hm T i).1; omega)
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
  have hnrow := new_row_log_factorial_bound hN
  have hl := log_factorial_normalization_lower (show 1 ≤ d*m+1 by omega)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hnrow hl
  have hrem : (d : ℝ)*(4/(3*(m : ℝ))) ≤ 2*(d : ℝ)/3 := by
    have hh : (4 : ℝ)/(3*(m : ℝ)) ≤ 2/3 := by apply (div_le_iff₀ (by positivity)).mpr; linarith
    nlinarith [mul_le_mul_of_nonneg_left hh hd0.le]
  have hlead : (d*m : ℝ)*Real.log ((d*m : ℝ)/2)+Real.log (d*m : ℝ) -
      ((d*m : ℝ)+1)*Real.log (((d*m : ℝ)+1)/2) ≤ Real.log 2 := by
    have hg := mul_le_mul_of_nonneg_left (Real.log_le_log hN0 (by linarith : (d*m : ℝ) ≤ (d*m : ℝ)+1))
      (show 0 ≤ (d*m : ℝ)+1 by positivity)
    rw [Real.log_div hN0.ne' (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div (by positivity : (d*m : ℝ)+1 ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    nlinarith
  nlinarith

theorem augBlockBregman_path_rate {d m : ℕ} (hd : 0 < d) (hm : 2 ≤ m) (T : Tournament d) :
    augBlockBregman T m / meanCycles (d*m+1) ≤
      2*Real.exp (11*(d : ℝ)/3+1/12) * (2*Real.pi)^(2*d+1) *
        ((d*m : ℝ)+1)^(2*d+2) * kappa T^(d*m) := by
  have hN : 1 ≤ d*m+1 := by omega
  have hN0 : (0 : ℝ) < (d*m : ℝ)+1 := by positivity
  have he := Real.exp_le_exp.mpr (augmented_log_sum_bound hd hm T)
  have hk : Real.exp ((d*m : ℝ)*Real.log (kappa T)) = kappa T^(d*m) := by
    rw [show (d*m : ℝ) = ((d*m : ℕ) : ℝ) by push_cast; rfl,
      Real.exp_nat_mul, Real.exp_log (kappa_pos T)]
  have hp : Real.exp ((2*(d : ℝ)+1)*Real.log (2*Real.pi*((d*m : ℝ)+1))) =
      (2*Real.pi*((d*m : ℝ)+1))^(2*d+1) := by
    rw [show 2*(d : ℝ)+1 = ((2*d+1 : ℕ) : ℝ) by push_cast; rfl,
      Real.exp_nat_mul, Real.exp_log (by positivity)]
  conv_rhs at he =>
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
      Real.exp_log (by positivity), hk, hp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_iff₀ (meanCycles_pos _)).mpr
  calc
    augBlockBregman T m ≤ _ := he
    _ = _ := by
      rw [factorial_normalization_eq _ hN, mul_pow]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      rw [show 2*d+2 = (2*d+1)+1 by omega, pow_succ]
      ring

end
end NonregularNormalization
