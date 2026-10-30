module

public import TournamentHamiltonian.NonregularNormalization.CycleRate

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace NonregularNormalization
open TournamentHamiltonian RegularOrientation UniformBlowup NonregularKappa NonregularRate NonregularDecay
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Add a new vertex labelled zero, with deterministic half weights to and from
all old vertices. This is a real matrix, not an assumed random-augmentation law. -/
def augmentMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => Fin.cases (Fin.cases 0 (fun _ => 1/2) j)
    (fun a => Fin.cases (1/2) (fun b => A a b) j) i

@[simp] theorem augment_zero_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    augmentMatrix A 0 j.succ = 1/2 := rfl
@[simp] theorem augment_succ_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    augmentMatrix A i.succ 0 = 1/2 := rfl
@[simp] theorem augment_succ_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    augmentMatrix A i.succ j.succ = A i j := rfl

/-- Extend an actual ordering by putting the new vertex first. -/
def extendOrdering {n : ℕ} (ψ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  ((finSuccEquiv n).trans (Equiv.optionCongr ψ)).trans (finSuccEquiv n).symm
@[simp] theorem extendOrdering_zero {n : ℕ} (ψ : Equiv.Perm (Fin n)) :
    extendOrdering ψ 0 = 0 := by simp [extendOrdering]
@[simp] theorem extendOrdering_succ {n : ℕ} (ψ : Equiv.Perm (Fin n)) (i : Fin n) :
    extendOrdering ψ i.succ = (ψ i).succ := by simp [extendOrdering]

def augmentedPathPermutation {n : ℕ} (ψ : Equiv.Perm (Fin (n+1))) : Equiv.Perm (Fin (n+2)) :=
  cycleFromOrdering (extendOrdering ψ)

theorem augmentedPathPermutation_injective {n : ℕ} :
    Function.Injective (augmentedPathPermutation (n := n)) := by
  intro ψ τ h
  have he : extendOrdering ψ = extendOrdering τ := by
    apply (orderingEquivMarkedCycle (n+1)).injective
    apply Prod.ext
    · exact Subtype.ext h
    · simp [orderingEquivMarkedCycle]
  apply Equiv.ext
  intro i
  have hi := congrArg (fun φ : Equiv.Perm (Fin (n+2)) => φ i.succ) he
  simpa using hi

/-- Closing the extended ordering gives exactly the two new half-edge factors,
with every original consecutive edge retained once. -/
theorem augmented_path_monomial {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (ψ : Equiv.Perm (Fin (n+1))) :
    (∏ j : Fin (n+2), augmentMatrix A (augmentedPathPermutation ψ j) j) =
      (∏ i : Fin n, A (ψ i.castSucc) (ψ i.succ))/4 := by
  have hzero : augmentedPathPermutation ψ 0 = (ψ (Fin.last n)).succ := by
    apply (augmentedPathPermutation ψ).symm.injective
    rw [Equiv.symm_apply_apply]
    have hx : (ψ (Fin.last n)).succ = extendOrdering ψ (Fin.last (n+1)) := by
      change (ψ (Fin.last n)).succ = extendOrdering ψ (Fin.last n).succ
      rw [extendOrdering_succ]
    rw [hx]
    change 0 = (cycleFromOrdering (extendOrdering ψ))⁻¹ (extendOrdering ψ (Fin.last (n+1)))
    rw [cycleFromOrdering_inv_apply, finRotate_last, extendOrdering_zero]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin (n+2))), hzero, augment_succ_zero]
  change (1/2 : ℝ) * brokenCycleWeight (augmentMatrix A) (cycleFromOrdering (extendOrdering ψ)) 0 = _
  have hb := brokenCycleWeight_cycleFromOrdering (augmentMatrix A) (extendOrdering ψ)
  simp only [extendOrdering_zero] at hb
  rw [hb, Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, extendOrdering_zero, extendOrdering_succ,
    augment_zero_succ, ← Fin.succ_castSucc, augment_succ_succ]
  ring

/-- The actual sum of all weighted path orderings, divided by four, embeds
monomial-by-monomial in the augmented matrix permanent. -/
theorem path_product_sum_le_augmented_permanent {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    (∑ ψ : Equiv.Perm (Fin (n+1)), ∏ i : Fin n, A (ψ i.castSucc) (ψ i.succ))/4 ≤
      (augmentMatrix A).permanent := by
  rw [Finset.sum_div, Matrix.permanent]
  simp_rw [← augmented_path_monomial]
  apply Finset.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ)
    (f := fun ψ : Equiv.Perm (Fin (n+1)) => ∏ j : Fin (n+2), augmentMatrix A (augmentedPathPermutation ψ j) j)
    (g := fun σ : Equiv.Perm (Fin (n+2)) => ∏ j : Fin (n+2), augmentMatrix A (σ j) j)
    augmentedPathPermutation augmentedPathPermutation_injective.injOn
    (Finset.subset_univ _) (fun _ _ => le_rfl)
  intro σ _ _
  apply Finset.prod_nonneg
  intro j _
  exact Fin.cases (by
    exact Fin.cases (by norm_num [augmentMatrix]) (fun _ => by norm_num) j)
    (fun i => Fin.cases (by norm_num) (fun k => hA i k) j) (σ j)

/-- The same injection using the frozen model's actual consecutive-step type. -/
theorem step_path_sum_le_augmented_permanent {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    (∑ ψ : Equiv.Perm (Fin n), ∏ r : Step n, A (ψ r.val.1) (ψ r.val.2))/4 ≤
      (augmentMatrix A).permanent := by
  cases n with
  | zero => omega
  | succ n =>
    have he (ψ : Equiv.Perm (Fin (n+1))) :
        (∏ r : Step (n+1), A (ψ r.val.1) (ψ r.val.2)) =
          ∏ i : Fin n, A (ψ i.castSucc) (ψ i.succ) := by
      apply Fintype.prod_equiv (stepEquiv (n+1))
      intro r
      apply congrArg₂ A
      · exact congrArg ψ (Fin.ext rfl)
      · exact congrArg ψ (Fin.ext r.property)
    simp_rw [he]
    exact path_product_sum_le_augmented_permanent A hA

/-- Actual uniform path expectation, not a hypothetical augmented expectation. -/
theorem uniform_avgPath_div_four_le_augmented_permanent {d m : ℕ} (hN : 1 ≤ d*m)
    (T : Tournament d) (e : Arrangement d m) :
    avgPath (m := m) T / 4 ≤
      (augmentMatrix ((uniformMatrix (m := m) T).submatrix e e)).permanent := by
  rw [avgPath_eq_weightedPathSum]
  have he : weightedPathSum (m := m) T =
      ∑ ψ : Equiv.Perm (Fin (d*m)), ∏ r : Step (d*m),
        weight T (e (ψ r.val.1)) (e (ψ r.val.2)) := by
    symm
    unfold weightedPathSum UniformBlowup.pathWeight
    apply Fintype.sum_equiv (arrangementEquiv e)
    intro ψ
    rfl
  rw [he]
  exact step_path_sum_le_augmented_permanent hN _ (fun i j => (uniform_weight_box T (e i) (e j)).1)

/-- Actual deterministic graph path count, with no random-edge independence. -/
theorem actual_pathCount_div_four_le_augmented_permanent {n : ℕ} (hn : 1 ≤ n)
    (T : Tournament n) :
    (TournamentHamiltonian.pathCount T : ℝ)/4 ≤ (augmentMatrix (adjacency T)).permanent := by
  cases n with
  | zero => omega
  | succ n =>
    rw [pathCount_eq_sum_consecutive_product]
    exact path_product_sum_le_augmented_permanent _ (fun i j => by unfold adjacency; split_ifs <;> norm_num)

end
end NonregularNormalization
