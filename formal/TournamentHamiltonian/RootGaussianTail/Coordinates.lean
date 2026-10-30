module

public import TournamentHamiltonian.RootGaussianTail.Base

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RootGaussianTail
open Matrix ForestGaussianIntegral
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def pairEnergy (p : ℕ) (x : Fin p → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (x i-x j)^2

theorem ordered_pair_energy (p : ℕ) (x : Fin p → ℝ) :
    (∑ i, ∑ j, (x i-x j)^2) = 2 * pairEnergy p x := by
  have hp (i j : Fin p) : (x i-x j)^2 =
      (if i < j then (x i-x j)^2 else 0) + (if j < i then (x i-x j)^2 else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j; simp
    · simp [h, not_lt_of_gt h]
  have hrev : (∑ i : Fin p, ∑ j : Fin p, if j < i then (x i-x j)^2 else 0) =
      ∑ i : Fin p, ∑ j : Fin p, if i < j then (x i-x j)^2 else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have he : (x j-x i)^2 = (x i-x j)^2 := by ring
    rw [he]
  calc
    (∑ i, ∑ j, (x i-x j)^2) = ∑ i, ∑ j,
        ((if i < j then (x i-x j)^2 else 0) + (if j < i then (x i-x j)^2 else 0)) := by
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hp i j))
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [hrev]
      simp only [pairEnergy, Finset.sum_filter]
      ring

theorem pairEnergy_moments (p : ℕ) (x : Fin p → ℝ) :
    pairEnergy p x = p * (∑ i, (x i)^2) - (∑ i, x i)^2 := by
  have hi (i : Fin p) : (∑ j, (x i-x j)^2) =
      p*(x i)^2 - 2*x i*(∑ j, x j) + ∑ j, (x j)^2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h := ordered_pair_energy p x
  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  simp only [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  nlinarith

theorem completeRoot_quadratic (n : ℕ) (x : Fin n → ℝ) :
    x ⬝ᵥ completeRoot n *ᵥ x = (n+1 : ℝ)*(∑ i, (x i)^2) - (∑ i, x i)^2 := by
  have hv (i : Fin n) : (completeRoot n *ᵥ x) i = (n+1 : ℝ)*x i - ∑ j, x j := by
    rw [completeRoot, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp [rootOnes, Matrix.mulVec, dotProduct]
  simp only [dotProduct, hv, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have he : (∑ i, x i*((n+1 : ℝ)*x i)) = (n+1 : ℝ)*∑ i, (x i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

/-- Literal unordered-pair kernel with the root fixed to zero. -/
theorem density_pair_energy (n : ℕ) (a : ℝ) (x : Fin n → ℝ) :
    density n a x = Real.exp (-a * pairEnergy (n+1) (Fin.cons 0 x)/2) := by
  rw [density_exp, Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [completeRoot_quadratic, pairEnergy_moments]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_pow (by decide : 2 ≠ 0),
    zero_add, Nat.cast_add, Nat.cast_one]
  congr 1
  ring
end RootGaussianTail
