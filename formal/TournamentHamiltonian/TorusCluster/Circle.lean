module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace TorusCluster
noncomputable section
open scoped BigOperators

/-- Genuine distance modulo π, not the distance of arbitrary real representatives. -/
def circleDist (x y : ℝ) : ℝ := ‖((x - y : ℝ) : AddCircle Real.pi)‖

lemma circleDist_nonneg (x y : ℝ) : 0 ≤ circleDist x y := norm_nonneg _
lemma circleDist_le_half (x y : ℝ) : circleDist x y ≤ Real.pi / 2 := by
  simpa [circleDist, abs_of_pos Real.pi_pos] using
    AddCircle.norm_le_half_period Real.pi Real.pi_ne_zero
lemma circleDist_symm (x y : ℝ) : circleDist x y = circleDist y x := by
  simp only [circleDist, AddCircle.coe_sub]
  exact norm_sub_rev _ _
lemma circleDist_triangle (x y z : ℝ) : circleDist x z ≤ circleDist x y + circleDist y z := by
  simp only [circleDist, AddCircle.coe_sub]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _
lemma circleDist_le_abs (x y : ℝ) : circleDist x y ≤ |x-y| := by
  exact QuotientAddGroup.norm_mk_le_norm
lemma circleDist_eq_abs {x y : ℝ} (h : |x-y| ≤ Real.pi/2) : circleDist x y = |x-y| := by
  apply (AddCircle.norm_coe_eq_abs_iff Real.pi Real.pi_ne_zero).2
  simpa [abs_of_pos Real.pi_pos] using h

/-- The chosen nearest representative of a difference from a fixed center. -/
def repr (x c : ℝ) : ℝ := x-c - (round (Real.pi⁻¹ * (x-c)) : ℝ) * Real.pi
lemma abs_repr (x c : ℝ) : |repr x c| = circleDist x c := by
  exact (AddCircle.norm_eq Real.pi).symm
lemma abs_repr_le_half (x c : ℝ) : |repr x c| ≤ Real.pi/2 := by
  rw [abs_repr]; exact circleDist_le_half _ _

lemma abs_cos_sub_int_pi (x : ℝ) (k : ℤ) :
    |Real.cos (x - k * Real.pi)| = |Real.cos x| := by
  rw [Real.cos_sub_int_mul_pi, abs_mul]
  simp

lemma cos_circleDist (x y : ℝ) : Real.cos (circleDist x y) = |Real.cos (x-y)| := by
  rw [← abs_repr, Real.cos_abs]
  have hn : 0 ≤ Real.cos (repr x y) := by
    apply Real.cos_nonneg_of_mem_Icc
    exact abs_le.mp (abs_repr_le_half x y)
  rw [← abs_of_nonneg hn]
  exact abs_cos_sub_int_pi (x-y) _

lemma abs_cos_le_of_separated {x y d : ℝ} (hd : 0 ≤ d) (hsep : d ≤ circleDist x y) :
    |Real.cos (x-y)| ≤ Real.cos d := by
  rw [← cos_circleDist]
  exact Real.cos_le_cos_of_nonneg_of_le_pi hd
    ((circleDist_le_half x y).trans (by linarith [Real.pi_pos])) hsep

lemma repr_sub_cos (x y c : ℝ) :
    |Real.cos (repr x c - repr y c)| = |Real.cos (x-y)| := by
  have he : repr x c - repr y c = x-y -
      ((round (Real.pi⁻¹*(x-c)) - round (Real.pi⁻¹*(y-c)) : ℤ) : ℝ)*Real.pi := by
    simp only [repr, Int.cast_sub]; ring
  rw [he, abs_cos_sub_int_pi]

lemma short_arc_real_difference {x y c a : ℝ}
    (hx : circleDist x c ≤ a) (hy : circleDist y c ≤ a) :
    |repr x c - repr y c| ≤ 2*a := by
  calc
    |repr x c - repr y c| ≤ |repr x c| + |repr y c| := abs_sub _ _
    _ ≤ 2*a := by rw [abs_repr, abs_repr]; linarith

/-- Fixed sixteen centers; the midpoint convention avoids a special wraparound bin. -/
def center (j : Fin 16) : ℝ := (2*(j.val : ℝ)+1)*Real.pi/32

lemma circleDist_sub_int_pi (x y : ℝ) (k : ℤ) :
    circleDist (x-k*Real.pi) y = circleDist x y := by
  unfold circleDist
  have he : x-k*Real.pi-y = x-y-k • Real.pi := by simp [zsmul_eq_mul]; ring
  rw [he, AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, sub_zero]

/-- Every real angle is in a radius π/32 arc about one of the fixed centers. -/
theorem sixteen_arc_cover (x : ℝ) : ∃ j : Fin 16, circleDist x (center j) ≤ Real.pi/32 := by
  let f : ℝ := Int.fract (x/Real.pi)
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  have hf1 : f < 1 := Int.fract_lt_one _
  let n : ℤ := ⌊16*f⌋
  have hn0 : 0 ≤ n := Int.floor_nonneg.mpr (by positivity)
  have hn16 : n < 16 := by
    apply Int.floor_lt.mpr
    norm_num
    linarith
  let j : Fin 16 := ⟨n.toNat, by omega⟩
  refine ⟨j, ?_⟩
  have hj : (j.val : ℝ) = n := by
    change (n.toNat : ℝ) = n
    exact_mod_cast Int.toNat_of_nonneg hn0
  have hl := Int.floor_le (16*f)
  have hu := Int.lt_floor_add_one (16*f)
  change (n : ℝ) ≤ 16*f at hl
  change 16*f < (n : ℝ)+1 at hu
  have hx : x-(⌊x/Real.pi⌋ : ℝ)*Real.pi = f*Real.pi := by
    change x-(⌊x/Real.pi⌋ : ℝ)*Real.pi =
      (x/Real.pi-(⌊x/Real.pi⌋ : ℝ))*Real.pi
    field_simp
  rw [← circleDist_sub_int_pi x (center j) ⌊x/Real.pi⌋, hx]
  apply (circleDist_le_abs _ _).trans
  rw [center, hj]
  apply abs_le.mpr
  constructor <;> nlinarith [Real.pi_pos]

lemma circleDist_repr (x y c : ℝ) :
    circleDist (repr x c) (repr y c) = circleDist x y := by
  have hx : ((repr x c : ℝ) : AddCircle Real.pi) = ((x-c : ℝ) : AddCircle Real.pi) := by
    simp only [repr, ← zsmul_eq_mul, AddCircle.coe_sub, AddCircle.coe_zsmul,
      AddCircle.coe_period, smul_zero, sub_zero]
  have hy : ((repr y c : ℝ) : AddCircle Real.pi) = ((y-c : ℝ) : AddCircle Real.pi) := by
    simp only [repr, ← zsmul_eq_mul, AddCircle.coe_sub, AddCircle.coe_zsmul,
      AddCircle.coe_period, smul_zero, sub_zero]
  simp only [circleDist, AddCircle.coe_sub, hx, hy]
  congr 1
  abel

end
end TorusCluster
