module

public import TournamentHamiltonian.WeightedMotif.Estimates

@[expose] public section

set_option autoImplicit false
namespace WeightedMotif
open Filter FiniteMotif
open scoped Topology
noncomputable section
attribute [local instance] Classical.propDecidable

def fallingRatio (k m : ℕ) : ℝ := (m.descFactorial k : ℝ)/(m : ℝ)^k

theorem fallingRatio_tendsto (k : ℕ) : Tendsto (fallingRatio k) atTop (𝓝 1) := by
  induction k with
  | zero =>
    convert tendsto_const_nhds (x := (1 : ℝ)) (f := atTop) using 1
    ext m
    simp [fallingRatio]
  | succ k ih =>
    have h : Tendsto (fun m : ℕ => (1-(k : ℝ)/m)*fallingRatio k m) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub
        (tendsto_natCast_atTop_atTop.const_div_atTop (k : ℝ))).mul ih
    apply h.congr'
    filter_upwards [eventually_ge_atTop (max k 1)] with m hm
    have hkm : k≤m := (le_max_left _ _).trans hm
    have hmR : (m : ℝ)≠0 := by exact_mod_cast (show m≠0 by omega)
    simp only [fallingRatio,Nat.descFactorial_succ,Nat.cast_mul,Nat.cast_sub hkm,pow_succ]
    field_simp

theorem firstMain_ratio (d m : ℕ) (hm : 0<m) :
    firstMain d m=(d : ℝ)*fallingRatio 3 m/((d : ℝ)-1/(m : ℝ))^2 := by
  have hmR : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  rw [firstMain_eq]
  simp only [Nat.cast_mul,fallingRatio]
  by_cases h : (d : ℝ)*m-1=0
  · have hh : (d : ℝ)-1/m=0 := by field_simp; nlinarith
    rw [h,hh]
    norm_num
  · field_simp

theorem secondMain_ratio (d m : ℕ) (hd : 0<d) (hm : 0<m) :
    secondMain d m=((d : ℝ)*((d : ℝ)-1)*(fallingRatio 3 m)^2+
      (d : ℝ)*fallingRatio 6 m)/((d : ℝ)-1/(m : ℝ))^4 := by
  have hmR : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  rw [secondMain_eq]
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_sub (show 1≤d from hd),Nat.cast_one,fallingRatio]
  by_cases h : (d : ℝ)*m-1=0
  · have hh : (d : ℝ)-1/m=0 := by field_simp; nlinarith
    rw [h,hh]
    norm_num
  · field_simp

theorem firstMain_tendsto (d : ℕ) (hd : 0<d) :
    Tendsto (firstMain d) atTop (𝓝 (1/(d : ℝ))) := by
  have hdR : (d : ℝ)≠0 := by exact_mod_cast hd.ne'
  have hden : Tendsto (fun m : ℕ => (d : ℝ)-1/(m : ℝ)) atTop (𝓝 (d : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := ((fallingRatio_tendsto 3).const_mul (d : ℝ)).div (hden.pow 2) (pow_ne_zero _ hdR)
  have hh : (d : ℝ)*1/(d : ℝ)^2=1/(d : ℝ) := by field_simp
  rw [hh] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact (firstMain_ratio d m (by omega)).symm

theorem secondMain_tendsto (d : ℕ) (hd : 0<d) :
    Tendsto (secondMain d) atTop (𝓝 ((1/(d : ℝ))^2)) := by
  have hdR : (d : ℝ)≠0 := by exact_mod_cast hd.ne'
  have hden : Tendsto (fun m : ℕ => (d : ℝ)-1/(m : ℝ)) atTop (𝓝 (d : ℝ)) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := (((fallingRatio_tendsto 3).pow 2).const_mul ((d : ℝ)*((d : ℝ)-1))).add
    ((fallingRatio_tendsto 6).const_mul (d : ℝ))
  have h := h.div (hden.pow 4) (pow_ne_zero _ hdR)
  have hh : ((d : ℝ)*((d : ℝ)-1)*1^2+(d : ℝ)*1)/(d : ℝ)^4=(1/(d : ℝ))^2 := by field_simp; ring
  rw [hh] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact (secondMain_ratio d m hd (by omega)).symm

theorem overlap_budget_tendsto (d : ℕ) :
    Tendsto (fun m : ℕ => 5*(d : ℝ)/m) atTop (𝓝 0) :=
  tendsto_natCast_atTop_atTop.const_div_atTop _

end
end WeightedMotif
