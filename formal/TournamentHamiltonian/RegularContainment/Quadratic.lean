module

public import TournamentHamiltonian.UniformTorusTail.Integration

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularContainment
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral PDGaussian TorusCluster RootGaussianTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable {n : ℕ}

/-- All-space Laplacian energy, not a local cosine comparison. -/
lemma laplacian_eq_graphEnergy {m : ℕ} (F : EdgeSet m) (y : Fin m → ℝ) :
    y ⬝ᵥ laplacian F *ᵥ y = graphEnergy (graph F) y Finset.univ := by
  have h := (graph F).lapMatrix_toLinearMap₂' ℝ y
  simp only [Matrix.toLinearMap₂'_apply'] at h
  have hg := twice_graphEnergy (graph F) y Finset.univ
  change y ⬝ᵥ laplacian F *ᵥ y = _ at h
  linarith

lemma root_quadratic_eq_graphEnergy (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    x ⬝ᵥ rootMatrix F *ᵥ x = graphEnergy (graph F)ᶜ (rootLift x) Finset.univ := by
  have hs := graphEnergy_compl_add (graph F) (rootLift x) Finset.univ
  rw [← laplacian_eq_graphEnergy, ← UniformTorusTail.pairEnergy_eq_completeEnergy,
    pairEnergy_moments] at hs
  rw [root_quadratic_identity, gaugeMatrix, Matrix.sub_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_sub,
    dotProduct_smul, ones_mulVec, dotProduct_smul, dot_one]
  have hsq : rootLift x ⬝ᵥ rootLift x = ∑ i, (rootLift x i)^2 := by simp [dotProduct, pow_two]
  rw [hsq]
  simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one] at hs ⊢
  linarith

lemma complete_quadratic_eq_energy (x : Fin n → ℝ) :
    x ⬝ᵥ completeRoot n *ᵥ x = completeEnergy (rootLift x) Finset.univ := by
  rw [← UniformTorusTail.pairEnergy_eq_completeEnergy, completeRoot_quadratic, pairEnergy_moments]
  simp [rootLift, Fin.sum_univ_succ]

/-- Exact global quadratic sandwich; it has no root-box hypothesis. -/
theorem quadratic_comparison (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    (1-4/((n+1:ℕ):ℝ))*(x ⬝ᵥ completeRoot n *ᵥ x) ≤ x ⬝ᵥ rootMatrix F *ᵥ x ∧
    x ⬝ᵥ rootMatrix F *ᵥ x ≤ x ⬝ᵥ completeRoot n *ᵥ x := by
  rw [root_quadratic_eq_graphEnergy, complete_quadratic_eq_energy]
  have hl := retained_energy_lower (graph F) (graph_degree_le_two F) (rootLift x) Finset.univ
  have hs := graphEnergy_compl_add (graph F) (rootLift x) Finset.univ
  have hn : 0 ≤ graphEnergy (graph F) (rootLift x) Finset.univ := by
    unfold graphEnergy
    apply Finset.sum_nonneg
    intro e _
    split_ifs
    · induction e using Sym2.ind with | _ i j => exact sq_nonneg _
    · exact le_rfl
  refine ⟨?_, by linarith⟩
  rw [completeEnergy_eq_variance]
  simp only [Finset.card_univ, Fintype.card_fin] at hl ⊢
  convert hl using 1
  have hm : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  field_simp

/-- Genuine full-space density sandwich. -/
theorem density_comparison (F : EdgeSet (n+1)) (x : Fin n → ℝ) :
    density n 1 x ≤ realKernel (rootMatrix F) 0 x ∧
    realKernel (rootMatrix F) 0 x ≤ density n (1-4/((n+1:ℕ):ℝ)) x := by
  have h := quadratic_comparison F x
  simp only [density_exp, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, one_mul,
    realKernel, zero_dotProduct, add_zero]
  constructor <;> apply Real.exp_le_exp.mpr <;> linarith [h.1, h.2]

end RegularContainment
