module

public import TournamentHamiltonian.ForestGaussianIntegral.CompleteRoot

@[expose] public section
set_option autoImplicit false
namespace ForestGaussianIntegral
open Matrix ForestGaussian
noncomputable section

theorem completeRoot_zero_det : (completeRoot 0).det = 1 := by simp

theorem completeRoot_order_two_det : (completeRoot 1).det = 1 := by
  rw [completeRoot_det 1 (by norm_num)]
  norm_num

theorem completeRoot_order_eight_det : (completeRoot 7).det = 262144 := by
  rw [completeRoot_det 7 (by norm_num)]
  norm_num

theorem completeRoot_order_eight_inverse_diag :
    (completeRoot 7)⁻¹ (0 : Fin 7) (0 : Fin 7) = 1/4 := by
  have h := scaled_completeRoot_inverse_entry 7 1 (by norm_num) (0 : Fin 7) 0
  norm_num at h ⊢
  exact h

theorem completeRoot_order_eight_inverse_offdiag :
    (completeRoot 7)⁻¹ (0 : Fin 7) (1 : Fin 7) = 1/8 := by
  have h := scaled_completeRoot_inverse_entry 7 1 (by norm_num) (0 : Fin 7) 1
  norm_num at h ⊢
  exact h

theorem rootFactor_empty (n : ℕ) (hm : 8 ≤ n+1) : rootFactor (emptyEdgeSet (n+1)) = 1 := by
  rw [rootFactor_eq_gaussianFactor _ hm, gaussianFactor_empty]

end
end ForestGaussianIntegral
