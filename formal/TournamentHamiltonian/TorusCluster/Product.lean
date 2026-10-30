module

public import TournamentHamiltonian.TorusCluster.Regions
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

set_option autoImplicit false
namespace TorusCluster
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

/-- A genuine unordered-edge absolute cosine factor. -/
def edgeFactor (x : Fin m → ℝ) : Sym2 (Fin m) → ℝ :=
  Sym2.lift ⟨fun i j => |Real.cos (x i-x j)|, fun i j => by
    dsimp
    rw [← Real.cos_neg (x i-x j)]
    congr 2
    ring⟩
@[simp] lemma edgeFactor_mk (x : Fin m → ℝ) (i j : Fin m) :
    edgeFactor x s(i,j) = |Real.cos (x i-x j)| := rfl
lemma edgeFactor_nonneg (x : Fin m → ℝ) (e : Sym2 (Fin m)) : 0 ≤ edgeFactor x e := by
  induction e using Sym2.ind with | _ i j => exact abs_nonneg _
lemma edgeFactor_le_one (x : Fin m → ℝ) (e : Sym2 (Fin m)) : edgeFactor x e ≤ 1 := by
  induction e using Sym2.ind with | _ i j => exact Real.abs_cos_le_one _

/-- Product over precisely the edges retained after deleting H. -/
def kernel (H : SimpleGraph (Fin m)) (x : Fin m → ℝ) : ℝ :=
  ∏ e ∈ Hᶜ.edgeFinset, edgeFactor x e
/-- The retained inside graph is preserved, not replaced by the bound 1. -/
def insideProduct (H : SimpleGraph (Fin m)) (x : Fin m → ℝ) (A : Finset (Fin m)) : ℝ :=
  ∏ e ∈ insideEdges H A, edgeFactor x e
lemma insideProduct_nonneg (H : SimpleGraph (Fin m)) (x : Fin m → ℝ) (A : Finset (Fin m)) :
    0 ≤ insideProduct H x A := Finset.prod_nonneg fun _ _ => edgeFactor_nonneg _ _

lemma kernel_le_subproduct (H : SimpleGraph (Fin m)) (x : Fin m → ℝ)
    (S : Finset (Sym2 (Fin m))) (hS : S ⊆ Hᶜ.edgeFinset) :
    kernel H x ≤ ∏ e ∈ S, edgeFactor x e := by
  exact Finset.prod_le_prod_of_subset_of_le_one₀ hS
    (fun e _ => edgeFactor_nonneg x e) (fun e _ _ => edgeFactor_le_one x e)

lemma cross_product_le (H : SimpleGraph (Fin m)) (x : Fin m → ℝ)
    (B A : Finset (Fin m)) (q : ℝ)
    (hq : ∀ i ∈ B, ∀ j ∈ A, |Real.cos (x i-x j)| ≤ q) :
    (∏ e ∈ crossEdges H B A, edgeFactor x e) ≤ q^(crossEdges H B A).card := by
  calc
    (∏ e ∈ crossEdges H B A, edgeFactor x e) ≤ ∏ _e ∈ crossEdges H B A, q := by
      apply Finset.prod_le_prod₀ (fun e _ => edgeFactor_nonneg _ _)
      intro e he
      obtain ⟨⟨i,j⟩, hp, rfl⟩ := Finset.mem_image.mp he
      have h := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hq i h.1 j h.2
    _ = _ := by simp

/-- General factor extraction: disjoint cross and inside edge products are both genuine factors. -/
lemma kernel_le_cross_times_inside (H : SimpleGraph (Fin m)) (x : Fin m → ℝ)
    (B I A : Finset (Fin m)) (hBI : Disjoint B I) (hBA : Disjoint B A)
    (q : ℝ) (hq : ∀ i ∈ B, ∀ j ∈ I, |Real.cos (x i-x j)| ≤ q) :
    kernel H x ≤ q^(crossEdges H B I).card * insideProduct H x A := by
  calc
    kernel H x ≤ ∏ e ∈ crossEdges H B I ∪ insideEdges H A, edgeFactor x e := by
      apply kernel_le_subproduct
      exact Finset.union_subset (crossEdges_subset H B I hBI) (insideEdges_subset H A)
    _ = (∏ e ∈ crossEdges H B I, edgeFactor x e) * insideProduct H x A := by
      rw [Finset.prod_union (cross_inside_disjoint H B I A hBA)]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (cross_product_le H x B I q hq) (insideProduct_nonneg H x A)

/-- Fixed constants in the proof plan, with no adjusted exponent. -/
def rho0 : ℝ := Real.cos (3*Real.pi/32)
def rho1 : ℝ := Real.cos (Real.pi/16)
def kappa0 : ℝ := -Real.log rho0
def kappa1 : ℝ := -Real.log rho1
lemma rho0_pos : 0 < rho0 := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]
lemma rho1_pos : 0 < rho1 := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]
lemma rho0_lt_one : rho0 < 1 := by
  simpa [rho0] using Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := 3*Real.pi/32)
    (by norm_num) (by linarith [Real.pi_pos]) (by positivity)
lemma rho1_lt_one : rho1 < 1 := by
  simpa [rho1] using Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := Real.pi/16)
    (by norm_num) (by linarith [Real.pi_pos]) (by positivity)
lemma kappa0_pos : 0 < kappa0 := neg_pos.mpr (Real.log_neg rho0_pos rho0_lt_one)
lemma kappa1_pos : 0 < kappa1 := neg_pos.mpr (Real.log_neg rho1_pos rho1_lt_one)

lemma pow_le_exp_neg_log_mul {q a : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (n : ℕ) (hn : a ≤ n) : q^n ≤ Real.exp (-(-Real.log q)*a) := by
  rw [show -(-Real.log q)*a = a*Real.log q by ring]
  have he : q^n = Real.exp ((n:ℝ)*Real.log q) := by rw [Real.exp_nat_mul, Real.exp_log hq0]
  rw [he, Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_right hn (Real.log_nonpos hq0.le hq1)

/-- Far pointwise bound with actual graph/angle definitions and actual degree counting. -/
theorem far_kernel_bound (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (hm : 64 ≤ m) (x : Fin m → ℝ) (c : ℝ)
    (hc : (m:ℝ)/16 ≤ (core x c).card) (hf : (m:ℝ)/4 ≤ (far x c).card) :
    kernel H x ≤ Real.exp (-kappa0*(m:ℝ)^2/128) := by
  have hd := far_core_disjoint x c
  have hcount := far_cross_count H hdegree hm (far x c) (core x c) hd hf hc
  calc
    kernel H x ≤ ∏ e ∈ crossEdges H (far x c) (core x c), edgeFactor x e :=
      kernel_le_subproduct H x _ (crossEdges_subset H _ _ hd)
    _ ≤ rho0^(crossEdges H (far x c) (core x c)).card := by
      apply cross_product_le
      intro i hi j hj
      exact abs_cos_le_of_separated (by positivity) (far_core_separated x c hi hj)
    _ ≤ Real.exp (-kappa0*((m:ℝ)^2/128)) :=
      pow_le_exp_neg_log_mul rho0_pos rho0_lt_one.le _ hcount
    _ = _ := by congr 1; ring

/-- Outlier pointwise bound explicitly keeps the entire actual inside-edge product.
No Gaussian normalization, integral, or tail theorem is asserted here. -/
theorem outlier_kernel_bound (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (hm : 64 ≤ m) (x : Fin m → ℝ) (c : ℝ)
    (hf : ((far x c).card : ℝ) < (m:ℝ)/4) :
    kernel H x ≤ Real.exp (-kappa1*(m:ℝ)*(outliers x c).card/2) *
      insideProduct H x (outer x c) := by
  have hBI := outliers_inner_disjoint x c
  have hBA := outliers_outer_disjoint x c
  have hcount := outlier_cross_count H hdegree hm (outliers x c) (inner x c) hBI
    (inner_large_of_not_far x c hf)
  calc
    kernel H x ≤ rho1^(crossEdges H (outliers x c) (inner x c)).card *
        insideProduct H x (outer x c) := by
      apply kernel_le_cross_times_inside H x _ _ _ hBI hBA
      intro i hi j hj
      exact abs_cos_le_of_separated (by positivity) (outlier_inner_separated x c hi hj)
    _ ≤ Real.exp (-kappa1*((m:ℝ)*(outliers x c).card/2)) * insideProduct H x (outer x c) := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_exp_neg_log_mul rho1_pos rho1_lt_one.le _ hcount) (insideProduct_nonneg H x _)
    _ = _ := by congr 2; ring

end
end TorusCluster
