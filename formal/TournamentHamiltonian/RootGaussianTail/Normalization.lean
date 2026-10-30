module

public import TournamentHamiltonian.RootGaussianTail.Tail

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootGaussianTail
open Matrix MeasureTheory ForestGaussianIntegral PDGaussian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sqrt_pow_exp (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Real.sqrt (a^n) = Real.exp ((n : ℝ)*Real.log a/2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (pow_pos ha n), Real.log_pow]
  congr 1
  ring

/-- Exact scaling law for the actual integral, including n=0. -/
theorem partition_scale_exp (n : ℕ) (a : ℝ) (ha : 0 < a) :
    partition n a = Real.exp (-(n : ℝ)*Real.log a/2) * partition n 1 := by
  let _ : DecidableEq (Fin n) := Classical.decEq _
  rw [partition_eq n a ha, partition_eq n 1 (by norm_num), one_smul, normalization, normalization]
  rw [Matrix.det_smul, Fintype.card_fin, Real.sqrt_mul (pow_nonneg ha.le n), sqrt_pow_exp a ha n]
  have he : -(n : ℝ)*Real.log a/2 = -((n : ℝ)*Real.log a/2) := by ring
  rw [he, Real.exp_neg]
  ring

theorem partition_scale_rpow (n : ℕ) (a : ℝ) (ha : 0 < a) :
    partition n a = a^(-(n : ℝ)/2) * partition n 1 := by
  rw [partition_scale_exp n a ha, Real.rpow_def_of_pos ha]
  congr 2
  ring

theorem perturbation_scale_pos (p : ℕ) (hp : 8 ≤ p) : 0 < 1 - 4/(p : ℝ) := by
  have hpr : (8 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by positivity
  exact sub_pos.mpr ((div_lt_one hp0).mpr (by linarith))

theorem perturbation_log_bound (n : ℕ) (hn : 7 ≤ n) :
    -(n : ℝ) * Real.log (1-4/(n+1 : ℝ))/2 ≤ 4 := by
  have hnr : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 < (n+1 : ℝ) := by positivity
  have hn3 : 0 < (n : ℝ)-3 := by linarith
  let a : ℝ := 1-4/(n+1 : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr ((div_lt_one hn1).mpr (by linarith))
  have hl : -Real.log a ≤ 1/a - 1 := by
    simpa only [Real.log_inv, one_div] using Real.log_le_sub_one_of_pos (inv_pos.mpr ha)
  have hbound : (n : ℝ)/2 * (1/a-1) ≤ 4 := by
    have he : (n : ℝ)/2 * (1/a-1) = 2*n/((n : ℝ)-3) := by
      have hea : a = ((n : ℝ)-3)/(n+1) := by
        dsimp [a]
        field_simp
        ring
      rw [hea]
      field_simp [ne_of_gt hn1, ne_of_gt hn3]
      ring
    rw [he]
    apply (div_le_iff₀ hn3).mpr
    linarith
  have hmul := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (n : ℝ)/2)
  dsimp [a] at hmul
  nlinarith

/-- For p≥8 the real normalized quadratic perturbation costs at most e^4. -/
theorem perturbation_normalization_loss (p : ℕ) (hp : 8 ≤ p) :
    Z p (1-4/(p : ℝ)) ≤ Real.exp 4 * Z p 1 := by
  have hp1 : 1 ≤ p := by omega
  have he : ((p-1 : ℕ) : ℝ)+1 = (p : ℝ) := by exact_mod_cast Nat.sub_add_cancel hp1
  unfold Z
  rw [partition_scale_exp _ _ (perturbation_scale_pos p hp)]
  apply mul_le_mul_of_nonneg_right _ (partition_pos _ 1 (by norm_num)).le
  apply Real.exp_le_exp.mpr
  have h := perturbation_log_bound (p-1) (by omega)
  rwa [he] at h

/-- Exact square-root expression retaining the root-gauge sqrt(p) normalization. -/
theorem Z_exact (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    Z p a = (Real.sqrt (2*Real.pi))^(p-1) /
      Real.sqrt (a^(p-1) * (p : ℝ)^(p-2)) := by
  unfold Z partition density
  have h := complete_partition (p-1) (by omega) a ha
  have he : ((p-1 : ℕ) : ℝ)+1 = (p : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ p)
  simpa only [he, Nat.sub_sub, Nat.reduceAdd] using h
end RootGaussianTail
