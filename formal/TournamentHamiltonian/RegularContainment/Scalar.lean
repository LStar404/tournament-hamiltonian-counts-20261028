module

public import TournamentHamiltonian.ForestGaussian.Boundary
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularContainment
open ForestGaussian Filter
open scoped Topology

/-- The target exponent is uniformly in [0,1], using actual arc budgets. -/
lemma target_exponent_bounds {m : ℕ} (F : EdgeSet m) (hm : 0 < m) :
    0 ≤ ((edgeCount F:ℝ)-sourceCount F)/m ∧ ((edgeCount F:ℝ)-sourceCount F)/m ≤ 1 := by
  have hp : (0:ℝ)<m := by exact_mod_cast hm
  have hs : (sourceCount F:ℝ)≤edgeCount F := by exact_mod_cast sourceCount_le_edgeCount F
  have hb : (edgeCount F:ℝ)+sourceCount F ≤ m := by exact_mod_cast edgeCount_add_sourceCount_le F
  constructor
  · exact div_nonneg (sub_nonneg.mpr hs) hp.le
  · apply (div_le_iff₀ hp).mpr
    have h0 : (0:ℝ)≤sourceCount F := by positivity
    linarith

/-- Γ is the determinant-times-phase ratio, not the pure characteristic factor. -/
lemma gaussianFactor_bounds {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) :
    Real.exp (-1) ≤ gaussianFactor F ∧ gaussianFactor F ≤ Real.exp 2 := by
  have h := gaussianFactor_uniform_log_error F hm
  have he := target_exponent_bounds F (by omega)
  have hmR : (8:ℝ)≤m := by exact_mod_cast hm
  have hb : 8/(m:ℝ) ≤ 1 := (div_le_one (by linarith : (0:ℝ)<m)).mpr hmR
  have hlohi := abs_le.mp h.2
  constructor
  · rw [← Real.exp_log h.1]
    exact Real.exp_le_exp.mpr (by linarith [he.1])
  · rw [← Real.exp_log h.1]
    exact Real.exp_le_exp.mpr (by linarith [he.2])

lemma exp_relative_error {u d e : ℝ} (hu : 0 < u) (_he : 0 ≤ e)
    (h : |Real.log u-d| ≤ e) : |u/Real.exp d-1| ≤ Real.exp e-1 := by
  have hid : u/Real.exp d=Real.exp (Real.log u-d) := by rw [Real.exp_sub,Real.exp_log hu]
  rw [hid]
  apply abs_le.mpr
  have hh := abs_le.mp h
  have hupper := Real.exp_le_exp.mpr hh.2
  have hlower := Real.exp_le_exp.mpr hh.1
  have hconv : 2 ≤ Real.exp e + Real.exp (-e) := by
    nlinarith [Real.add_one_le_exp e, Real.add_one_le_exp (-e)]
  constructor <;> linarith

lemma gaussianFactor_relative_error {m : ℕ} (F : EdgeSet m) (hm : 8 ≤ m) :
    |gaussianFactor F/Real.exp (((edgeCount F:ℝ)-sourceCount F)/m)-1| ≤
      Real.exp (8/(m:ℝ))-1 := by
  have h := gaussianFactor_uniform_log_error F hm
  exact exp_relative_error h.1 (by positivity) h.2

/-- Two relative errors of size κ lose at most 4κ in their quotient. -/
lemma quotient_budget {u v κ : ℝ} (hκ : 0 ≤ κ) (hk : κ ≤ 1/2)
    (hu : |u-1| ≤ κ) (hv : |v-1| ≤ κ) :
    1/2 ≤ v ∧ |u/v-1| ≤ 4*κ ∧ |u/v| ≤ 3 := by
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have hvpos : 0 < v := by linarith
  have huv : |u-v| ≤ 2*κ := by
    calc |u-v| = |(u-1)-(v-1)| := by congr 1; ring
         _ ≤ |u-1|+|v-1| := abs_sub _ _
         _ ≤ _ := by linarith
  have hratio : |u/v-1| ≤ 4*κ := by
    rw [div_sub_one hvpos.ne', abs_div, abs_of_pos hvpos]
    apply (div_le_iff₀ hvpos).mpr
    nlinarith
  refine ⟨by linarith,hratio,?_⟩
  calc |u/v| = |(u/v-1)+1| := by ring_nf
       _ ≤ |u/v-1|+|1| := abs_add_le _ _
       _ ≤ 3 := by norm_num; linarith

/-- Strictly verified final constants: 4κ + 3ε. -/
lemma combined_quotient_budget {u v w κ ε : ℝ} (hκ : 0 ≤ κ) (hk : κ ≤ 1/2)
    (hu : |u-1| ≤ κ) (hv : |v-1| ≤ κ) (hw : |w-1| ≤ ε) :
    |u/v*w-1| ≤ 4*κ+3*ε := by
  have hq := quotient_budget hκ hk hu hv
  have he : 0 ≤ ε := (abs_nonneg _).trans hw
  calc
    |u/v*w-1| = |(u/v-1)+(u/v)*(w-1)| := by congr 1; ring
    _ ≤ |u/v-1|+|u/v| * |w-1| := by simpa only [abs_mul] using abs_add_le (u/v-1) ((u/v)*(w-1))
    _ ≤ 4*κ+3*ε := add_le_add hq.2.1 (mul_le_mul hq.2.2 hw (abs_nonneg _) (by norm_num))

lemma cancel_small_probability_factor {p x y t : ℝ} (hp : p ≠ 0) :
    (p*x/y)/(p*t) = x/y/t := by field_simp

end RegularContainment
