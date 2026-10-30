module

public import TournamentHamiltonian.GaussianFactorialRecovery

@[expose] public section

set_option autoImplicit false
namespace PaperGaussianRecovery
open TournamentHamiltonian
open scoped BigOperators
noncomputable section

/-- The step estimate retains the paper's exact 1/(1−α), rather than replacing it by 2. -/
theorem recovery_step_log_fine (n k : ℕ) (hn : 0<n) (α : ℝ) (hα : α<1)
    (hk : (k:ℝ)≤α*n) :
    Real.log ((n:ℝ)/(n-k:ℝ)) ≤ (k:ℝ)/((n:ℝ)*(1-α)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hden : 0<(n:ℝ)*(1-α) := mul_pos hnR (by linarith)
  have hdenle : (n:ℝ)*(1-α)≤n-k := by nlinarith
  have hp : (0:ℝ)<n-k := hden.trans_le hdenle
  have hlog := Real.log_le_sub_one_of_pos (div_pos hnR hp)
  have he : (n:ℝ)/(n-k:ℝ)-1=(k:ℝ)/(n-k:ℝ) := by field_simp; ring
  rw [he] at hlog
  exact hlog.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg k) hden hdenle)

/-- Exact factorial second-order logarithmic budget for the actual descending-factorial ratio. -/
theorem factorialRecoveryRatio_log_fine (n k : ℕ) (hn : 0<n) (α : ℝ) (hα : α<1)
    (hk : (k:ℝ)≤α*n) :
    Real.log (factorialRecoveryRatio n k) ≤
      (k:ℝ)*((k:ℝ)-1)/(2*(n:ℝ)*(1-α)) := by
  induction k with
  | zero => simp [factorialRecoveryRatio]
  | succ k ih =>
    have hnR : (0:ℝ)<n := by exact_mod_cast hn
    have hknR : (k:ℝ)<n := by push_cast at hk; nlinarith
    have hkn : k<n := by exact_mod_cast hknR
    have hkprev : (k:ℝ)≤α*n := by push_cast at hk; linarith
    have hd : (0:ℝ)<n-k := by linarith
    rw [factorialRecoveryRatio_succ n k hn hkn,
      Real.log_mul (div_pos hnR hd).ne' (factorialRecoveryRatio_pos n k hn hkn.le).ne']
    calc
      _ ≤ (k:ℝ)/((n:ℝ)*(1-α))+(k:ℝ)*((k:ℝ)-1)/(2*(n:ℝ)*(1-α)) :=
        add_le_add (recovery_step_log_fine n k hn α hα hkprev) (ih hkprev)
      _ = _ := by push_cast; field_simp [hnR.ne', (sub_pos.mpr hα).ne']; ring

/-- The paper's pointwise recovery bound with k(k−1)/(2n(1−α)). -/
theorem factorialRecoveryRatio_sub_one_fine (n k : ℕ) (hn : 0<n)
    (α σ : ℝ) (hα : α≤1/4) (hσ : 1<σ) (hασ : α≤Real.log σ)
    (hk : (k:ℝ)≤α*n) :
    0≤factorialRecoveryRatio n k-1 ∧
      factorialRecoveryRatio n k-1 ≤
        ((k:ℝ)*((k:ℝ)-1)/(2*(n:ℝ)*(1-α)))*σ^k := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hhalf : 2*k≤n := by
    have ha := mul_le_mul_of_nonneg_right hα hnR.le
    have ht : (2:ℝ)*k≤n := by nlinarith
    exact_mod_cast ht
  have hp := factorialRecoveryRatio_pos n k hn (by omega)
  have h1 := factorialRecoveryRatio_one_le n k hn (by omega)
  have hwindow : (k:ℝ)/n≤Real.log σ := by
    apply (div_le_iff₀ hnR).mpr
    exact hk.trans (mul_le_mul_of_nonneg_right hασ hnR.le)
  have hlog0 := Real.log_nonneg h1
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
  rw [mul_sub,mul_one,mul_inv_cancel₀ hp.ne'] at h
  have hprod := mul_le_mul (factorialRecoveryRatio_le_pow n k hn hhalf σ hσ hwindow)
    (factorialRecoveryRatio_log_fine n k hn α (by linarith) hk)
    hlog0 (pow_nonneg (by linarith : 0≤σ) k)
  exact ⟨by linarith,h.trans (hprod.trans_eq (mul_comm _ _))⟩

end
end PaperGaussianRecovery
