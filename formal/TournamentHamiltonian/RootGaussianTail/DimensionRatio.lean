module

public import TournamentHamiltonian.RootGaussianTail.Normalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootGaussianTail
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem Z_one_exp (p : ℕ) (hp : 2 ≤ p) :
    Z p 1 = Real.exp (((p : ℝ)-1)*Real.log (2*Real.pi)/2 -
      ((p : ℝ)-2)*Real.log p/2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [Z_exact p hp 1 (by norm_num), one_pow, one_mul, sqrt_pow_exp _ hp0,
    Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity : 0 < 2*Real.pi),
    ← Real.exp_nat_mul, ← Real.exp_sub]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_sub hp]
  norm_num
  ring

/-- The explicit sqrt(p) is the root-gauge Jacobian normalization, not an extra loss. -/
theorem Z_one_rpow (p : ℕ) (hp : 2 ≤ p) :
    Z p 1 = Real.sqrt p * (2*Real.pi/(p : ℝ))^(((p : ℝ)-1)/2) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [Z_one_exp p hp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0,
    Real.rpow_def_of_pos (by positivity : 0 < 2*Real.pi/(p : ℝ)), ← Real.exp_add,
    Real.log_div (by positivity) (ne_of_gt hp0)]
  congr 1
  ring

theorem Z_scaled_rpow (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    Z p a = a^(-((p : ℝ)-1)/2) * Real.sqrt p *
      (2*Real.pi/(p : ℝ))^(((p : ℝ)-1)/2) := by
  change partition (p-1) a = _
  rw [partition_scale_rpow _ a ha]
  change a^(-((p-1 : ℕ) : ℝ)/2) * Z p 1 = _
  rw [Z_one_rpow p hp, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  ring

/-- The dimension change includes the root-gauge normalization, with no extra sqrt(p). -/
theorem Z_dimension_ratio (q m : ℕ) (hq : 2 ≤ q) (hqm : q ≤ m) :
    Z q 1 / Z m 1 ≤ (Real.exp 1 * m / (2*Real.pi)) ^ (((m : ℝ)-q)/2) := by
  have hm : 2 ≤ m := hq.trans hqm
  have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hmr : (q : ℝ) ≤ m := by exact_mod_cast hqm
  have hq0 : (0 : ℝ) < q := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hpi : 0 < 2*Real.pi := by positivity
  have hlog : Real.log (m : ℝ)-Real.log q ≤ ((m : ℝ)-q)/q := by
    have h := Real.log_le_sub_one_of_pos (div_pos hm0 hq0)
    rw [Real.log_div (ne_of_gt hm0) (ne_of_gt hq0)] at h
    have he : (m : ℝ)/q-1 = ((m : ℝ)-q)/q := by field_simp
    rwa [he] at h
  have hs : ((q : ℝ)-2)*(Real.log m-Real.log q) ≤ (m : ℝ)-q := by
    calc
      ((q : ℝ)-2)*(Real.log m-Real.log q) ≤ ((q : ℝ)-2)*(((m : ℝ)-q)/q) :=
        mul_le_mul_of_nonneg_left hlog (by linarith)
      _ ≤ q*(((m : ℝ)-q)/q) := mul_le_mul_of_nonneg_right (by linarith)
        (div_nonneg (sub_nonneg.mpr hmr) hq0.le)
      _ = (m : ℝ)-q := by field_simp
  rw [Z_one_exp q hq, Z_one_exp m hm, ← Real.exp_sub,
    Real.rpow_def_of_pos (by positivity : 0 < Real.exp 1 * m / (2*Real.pi))]
  rw [Real.log_div (by positivity) (ne_of_gt hpi),
    Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hm0), Real.log_exp]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Vertex-deletion form requested for m-r≥2. -/
theorem Z_deletion_ratio (m r : ℕ) (h : 2 ≤ m-r) :
    Z (m-r) 1 / Z m 1 ≤ (Real.exp 1 * m / (2*Real.pi)) ^ ((r : ℝ)/2) := by
  have hratio := Z_dimension_ratio (m-r) m h (Nat.sub_le _ _)
  have hr : r ≤ m := by omega
  have he : (m : ℝ)-((m-r : ℕ) : ℝ) = (r : ℝ) := by
    rw [Nat.cast_sub hr]
    ring
  rwa [he] at hratio
end RootGaussianTail
