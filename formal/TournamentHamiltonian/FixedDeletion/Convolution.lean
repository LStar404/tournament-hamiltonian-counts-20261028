module

public import TournamentHamiltonian.FixedDeletion.Reindex

@[expose] public section

set_option autoImplicit false
namespace FixedDeletion
open TournamentHamiltonian
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α] [DecidableEq α]

def minorRatio (D : Matrix α α ℝ) (V : Finset α) : ℝ := (principal D V).permanent/D.permanent

/-- An exact ambient sum, with no assumed asymptotic or stochastic retained matrix. -/
def difference (D : Matrix α α ℝ) (U : Finset α) (f : Finset α → ℝ) : ℝ :=
  ∑ V : Finset α, if Disjoint U V then
    f V*(minorRatio D (U∪V)-minorRatio D V) else -f V*minorRatio D V

theorem sum_disjoint_eq (U : Finset α) (f : Finset α → ℝ) :
    (∑ V : {V : Finset α // Disjoint U V}, f V.val) =
      ∑ V : Finset α, if Disjoint U V then f V else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun V => Disjoint U V)) (by simp) f]
  rw [Finset.sum_filter]

theorem difference_eq (D : Matrix α α ℝ) (U : Finset α) (f : Finset α → ℝ) :
    difference D U f =
      (∑ V : {V : Finset α // Disjoint U V}, f V.val*minorRatio D (U∪V.val)) -
        ∑ V : Finset α, f V*minorRatio D V := by
  rw [sum_disjoint_eq U (fun V => f V*minorRatio D (U∪V)), ← Finset.sum_sub_distrib]
  unfold difference
  apply Finset.sum_congr rfl
  intro V _
  split_ifs <;> ring

theorem cycle_difference_eq (D : Matrix α α ℝ) (U : Finset α) :
    ((Fintype.card (Uᶜ : Finset α) : ℝ)*WeightedCycle.cyc (principal D U)-
      (Fintype.card α : ℝ)*WeightedCycle.cyc D)/D.permanent = difference D U (cycleCoeff D) := by
  rw [deleted_cycle_convolution, cycle_convolution, difference_eq, sub_div, Finset.sum_div, Finset.sum_div]
  simp only [minorRatio, mul_div_assoc]

theorem path_difference_eq (D : Matrix α α ℝ) (U : Finset α) :
    (WeightedCycle.path (principal D U)-WeightedCycle.path D)/((Fintype.card α : ℝ)*D.permanent) =
      difference D U (fun V => pathCoeff D V/(Fintype.card α : ℝ)) := by
  rw [deleted_path_convolution, path_convolution, difference_eq, sub_div, Finset.sum_div, Finset.sum_div]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro V _ <;> unfold minorRatio <;> ring

end
end FixedDeletion
