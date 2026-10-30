module

public import TournamentHamiltonian.FrobeniusCp.Algebra
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FrobeniusCp
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {𝕜 n m : Type*} [RCLike 𝕜] [Fintype n] [Fintype m]

def frobenius (K : Matrix n m 𝕜) : ℝ := Real.sqrt (∑ i, ∑ j, ‖K i j‖ ^ 2)

lemma frobenius_nonneg (K : Matrix n m 𝕜) : 0 ≤ frobenius K := Real.sqrt_nonneg _

lemma frobenius_sq (K : Matrix n m 𝕜) :
    frobenius K ^ 2 = ∑ i, ∑ j, ‖K i j‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma entry_le_frobenius (K : Matrix n m 𝕜) (i : n) (j : m) : ‖K i j‖ ≤ frobenius K := by
  apply (sq_le_sq₀ (norm_nonneg _) (frobenius_nonneg _)).mp
  rw [frobenius_sq]
  exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖K i k‖) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg ‖K k l‖)
      (Finset.mem_univ i))

lemma det_entry_bound [DecidableEq n] (K : Matrix n n 𝕜) (δ : ℝ)
    (_hδ : 0 ≤ δ) (hK : ∀ i j, ‖K i j‖ ≤ δ) :
    ‖K.det‖ ≤ (Fintype.card n).factorial * δ ^ Fintype.card n := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm n, ‖Equiv.Perm.sign σ • ∏ i, K (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ∏ i, ‖K (σ i) i‖ := by simp only [norm_units_zsmul, norm_prod]
    _ ≤ ∑ _σ : Equiv.Perm n, δ ^ Fintype.card n := by
      apply Finset.sum_le_sum
      intro σ _
      simpa only [Finset.prod_const, Finset.card_univ] using Finset.prod_le_prod₀ (s := (Finset.univ : Finset n)) (fun i _ => norm_nonneg (K (σ i) i)) (fun i _ => hK (σ i) i)
    _ = _ := by simp [Fintype.card_perm]

lemma principalMinor_bound [DecidableEq n] (K : Matrix n n 𝕜) (s : Finset n) :
    ‖principalMinor K s‖ ≤ s.card.factorial * frobenius K ^ s.card := by
  simpa only [principalMinor, Fintype.card_coe] using
    det_entry_bound (K.submatrix (Subtype.val : s → n) Subtype.val)
      (frobenius K) (frobenius_nonneg K) (fun i j => entry_le_frobenius K i j)

end FrobeniusCp
