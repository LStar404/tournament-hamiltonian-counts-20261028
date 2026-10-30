module

public import TournamentHamiltonian.WeightedMotif.Limits

@[expose] public section

set_option autoImplicit false
namespace MotifExp
open WeightedMotif FiniteMotif TournamentHamiltonian Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The finite weighted Cauchy-Schwarz inequality, with a genuine normalized law. -/
theorem expect_abs_le_sqrt {α : Type*} [Fintype α] (w f : α → ℝ)
    (hw : ∀ x,0≤w x) (hZ : 0<total w) :
    expect w (fun x => |f x|)≤Real.sqrt (expect w (fun x => (f x)^2)) := by
  have hp := mass_nonneg hw hZ
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ hp
    (fun x => mul_nonneg (hp x) (sq_nonneg (f x)))
  have he (x : α) : Real.sqrt (mass w x)*Real.sqrt (mass w x*(f x)^2)=mass w x*|f x| := by
    rw [Real.sqrt_mul (hp x),Real.sqrt_sq_eq_abs,←mul_assoc,Real.mul_self_sqrt (hp x)]
  simpa only [he,mass_sum hZ,Real.sqrt_one,one_mul,expect] using h

theorem exp_difference_le {x y D : ℝ} (hx : x≤D) (hy : y≤D) :
    |Real.exp x-Real.exp y|≤Real.exp D*|x-y| := by
  have oneSide {a b : ℝ} (hab : a≤b) (hb : b≤D) :
      Real.exp b-Real.exp a≤Real.exp D*(b-a) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a-b)) (Real.exp_pos b).le
    have he : Real.exp b*Real.exp (a-b)=Real.exp a := by rw [←Real.exp_add]; congr 1; ring
    rw [he] at h
    have hu := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb) (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total x y with h|h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h)),abs_of_nonpos (sub_nonpos.mpr h)]
    simpa only [neg_sub] using oneSide h hy
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),abs_of_nonneg (sub_nonneg.mpr h)]
    exact oneSide h hx

theorem expect_exp_error {α : Type*} [Fintype α] (w f : α → ℝ) (c D : ℝ)
    (hw : ∀ x,0≤w x) (hZ : 0<total w) (hf : ∀ x,f x≤D) (hc : c≤D) :
    |expect w (fun x => Real.exp (f x))-Real.exp c|≤
      Real.exp D*Real.sqrt (expect w (fun x => (f x-c)^2)) := by
  have he : expect w (fun x => Real.exp (f x))-Real.exp c=
      expect w (fun x => Real.exp (f x)-Real.exp c) := by
    simp only [expect,mul_sub,Finset.sum_sub_distrib]
    rw [←Finset.sum_mul,mass_sum hZ,one_mul]
  rw [he]
  calc |expect w (fun x => Real.exp (f x)-Real.exp c)|
      ≤ expect w (fun x => |Real.exp (f x)-Real.exp c|) := by
        unfold expect
        calc |∑ x,mass w x*(Real.exp (f x)-Real.exp c)|
            ≤ ∑ x,|mass w x*(Real.exp (f x)-Real.exp c)| := Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp only [abs_mul,abs_of_nonneg (mass_nonneg hw hZ _)]
    _ ≤ expect w (fun x => Real.exp D*|f x-c|) :=
      expect_mono hw hZ (fun x => exp_difference_le (hf x) hc)
    _ = Real.exp D*expect w (fun x => |f x-c|) := expect_mul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (expect_abs_le_sqrt w (fun x => f x-c) hw hZ) (Real.exp_pos D).le

theorem count_div_bound {d m : ℕ} {a : ℕ} (ha : a≤d*m) (hm : 0<m) :
    0≤(a : ℝ)/m ∧ (a : ℝ)/m≤d := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  refine ⟨by positivity,(div_le_iff₀ hmR).mpr ?_⟩
  exact_mod_cast ha

theorem inv_degree_bound (d : ℕ) (hd : 0<d) : (1/(d : ℝ))≤d := by
  have hdR : (1 : ℝ)≤d := by exact_mod_cast hd
  apply (div_le_iff₀ (by linarith : (0 : ℝ)<d)).mpr
  nlinarith

def cycleExp {d m : ℕ} (T : Tournament d) : ℝ :=
  expect (cycleWeight (m:=m) T) (fun σ => Real.exp ((cycleA σ : ℝ)/m))
def pathExp {d m : ℕ} (T : Tournament d) : ℝ :=
  expect (pathWeight (m:=m) T) (fun π => Real.exp ((pathA π : ℝ)/m))

theorem cycle_exp_bound {d m : ℕ} (T : Tournament d) (hd : 0<d) (hm : 0<m)
    (hZ : 0<total (cycleWeight (m:=m) T)) :
    |cycleExp (m:=m) T-Real.exp (1/(d : ℝ))|≤
      Real.exp (d : ℝ)*Real.sqrt (cycleMeanSquare (m:=m) T) :=
  expect_exp_error _ _ _ _ (cycleWeight_nonneg T) hZ
    (fun σ => (count_div_bound (cycle_bounds σ).1 hm).2) (inv_degree_bound d hd)

theorem path_exp_bound {d m : ℕ} (T : Tournament d) (hd : 0<d) (hm : 0<m)
    (hZ : 0<total (pathWeight (m:=m) T)) :
    |pathExp (m:=m) T-Real.exp (1/(d : ℝ))|≤
      Real.exp (d : ℝ)*Real.sqrt (pathMeanSquare (m:=m) T) :=
  expect_exp_error _ _ _ _ (pathWeight_nonneg T) hZ
    (fun π => (count_div_bound (path_bounds π).1 hm).2) (inv_degree_bound d hd)

theorem cycle_exp_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => cycleExp (m:=m) T) atTop (𝓝 (Real.exp (1/(d : ℝ)))) := by
  have h := ((cycle_meanSquare_tendsto T hT hd).sqrt).const_mul (Real.exp (d : ℝ))
  simp only [Real.sqrt_zero,mul_zero] at h
  have he : Tendsto (fun m : ℕ => |cycleExp (m:=m) T-Real.exp (1/(d : ℝ))|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ h
    filter_upwards [actual_positive T hT hd,eventually_ge_atTop 1] with m hm h1
    exact cycle_exp_bound T hd (by omega) hm.1
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using he)

theorem path_exp_tendsto {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) :
    Tendsto (fun m : ℕ => pathExp (m:=m) T) atTop (𝓝 (Real.exp (1/(d : ℝ)))) := by
  have h := ((path_meanSquare_tendsto T hT hd).sqrt).const_mul (Real.exp (d : ℝ))
  simp only [Real.sqrt_zero,mul_zero] at h
  have he : Tendsto (fun m : ℕ => |pathExp (m:=m) T-Real.exp (1/(d : ℝ))|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ h
    filter_upwards [actual_positive T hT hd,eventually_ge_atTop 1] with m hm h1
    exact path_exp_bound T hd (by omega) hm.2
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using he)

end
end MotifExp
