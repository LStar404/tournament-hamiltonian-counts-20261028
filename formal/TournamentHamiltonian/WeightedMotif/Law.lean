module

public import TournamentHamiltonian.FiniteMotif.Actual

@[expose] public section

set_option autoImplicit false
namespace WeightedMotif
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- Raw total weight, not assumed to be positive. -/
def total (w : α → ℝ) : ℝ := ∑ x, w x
/-- Totalized normalized mass. Probability claims below require total > 0. -/
def mass (w : α → ℝ) (x : α) : ℝ := w x / total w
def expect (w : α → ℝ) (f : α → ℝ) : ℝ := ∑ x, mass w x*f x
def event (w : α → ℝ) (P : α → Prop) : ℝ := expect w (fun x => if P x then 1 else 0)

theorem mass_nonneg {w : α → ℝ} (hw : ∀ x,0≤w x) (hZ : 0<total w) (x : α) :
    0≤mass w x := div_nonneg (hw x) hZ.le

theorem mass_sum {w : α → ℝ} (hZ : 0<total w) : ∑ x,mass w x=1 := by
  simp only [mass,←Finset.sum_div,total]
  exact div_self hZ.ne'

/-- A genuine finite law: nonnegative masses and total exactly one. -/
theorem normalized_law {w : α → ℝ} (hw : ∀ x,0≤w x) (hZ : 0<total w) :
    (∀ x,0≤mass w x) ∧ (∑ x,mass w x)=1 := ⟨mass_nonneg hw hZ,mass_sum hZ⟩

theorem expect_const (w : α → ℝ) (hZ : 0<total w) (c : ℝ) : expect w (fun _ => c)=c := by
  simp only [expect,←Finset.sum_mul,mass_sum hZ,one_mul]

theorem expect_add (w : α → ℝ) (f g : α → ℝ) :
    expect w (fun x => f x+g x)=expect w f+expect w g := by
  simp only [expect,mul_add,Finset.sum_add_distrib]

theorem expect_mul (w : α → ℝ) (f : α → ℝ) (c : ℝ) :
    expect w (fun x => c*f x)=c*expect w f := by
  simp only [expect,Finset.mul_sum]; congr 1; ext x; ring

theorem expect_div (w : α → ℝ) (f : α → ℝ) (c : ℝ) :
    expect w (fun x => f x/c)=expect w f/c := by
  simp only [expect,mul_div_assoc,Finset.sum_div]

theorem expect_nonneg {w : α → ℝ} (hw : ∀ x,0≤w x) (hZ : 0<total w)
    {f : α → ℝ} (hf : ∀ x,0≤f x) : 0≤expect w f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (mass_nonneg hw hZ x) (hf x))

theorem expect_mono {w : α → ℝ} (hw : ∀ x,0≤w x) (hZ : 0<total w)
    {f g : α → ℝ} (h : ∀ x,f x≤g x) : expect w f≤expect w g :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (mass_nonneg hw hZ x))

theorem event_eq (w : α → ℝ) (P : α → Prop) :
    event w P=(∑ x,if P x then w x else 0)/total w := by
  simp only [event,expect,mass,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem event_bounds {w : α → ℝ} (hw : ∀ x,0≤w x) (hZ : 0<total w) (P : α → Prop) :
    0≤event w P ∧ event w P≤1 := by
  constructor
  · exact expect_nonneg hw hZ (by intro x; split_ifs <;> norm_num)
  · calc event w P ≤ expect w (fun _ => 1) := expect_mono hw hZ (by intro x; split_ifs <;> norm_num)
         _ = 1 := expect_const w hZ 1

/-- Finite first-moment identity; no independence or positivity is needed for the algebra. -/
theorem expect_count (w : α → ℝ) (P : ι → α → Prop)
    [∀ x,DecidablePred (fun i => P i x)] :
    expect w (fun x => ((Finset.univ.filter (fun i => P i x)).card : ℝ)) =
      ∑ i,event w (P i) := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  push_cast
  unfold event expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : P i x <;> simp [h]

/-- Summing uniformly controlled event errors and dividing by a positive scale. -/
theorem sum_error (p : ι → ℝ) (r s ε : ℝ) (hr : 0<r) (hs : 0<s)
    (hp : ∀ i,|s*p i-1|≤ε) :
    |(∑ i,p i)/r-(Fintype.card ι : ℝ)/(r*s)|≤ε*(Fintype.card ι : ℝ)/(r*s) := by
  have hsum : |∑ i,(s*p i-1)|≤(Fintype.card ι : ℝ)*ε := by
    calc |∑ i,(s*p i-1)| ≤ ∑ i,|s*p i-1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι,ε := Finset.sum_le_sum (fun i _ => hp i)
      _ = _ := by simp
  have hid : (∑ i,p i)/r-(Fintype.card ι : ℝ)/(r*s)=
      (∑ i,(s*p i-1))/(r*s) := by
    simp only [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    field_simp
  rw [hid,abs_div,abs_of_pos (mul_pos hr hs)]
  simpa only [mul_comm ε] using div_le_div_of_nonneg_right hsum (mul_pos hr hs).le

end
end WeightedMotif
