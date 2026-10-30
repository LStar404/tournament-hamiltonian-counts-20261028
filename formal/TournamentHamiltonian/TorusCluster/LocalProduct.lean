module

public import TournamentHamiltonian.TorusCluster.Quadratic

@[expose] public section

set_option autoImplicit false
namespace TorusCluster
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

lemma inside_energy_eq (H : SimpleGraph (Fin m)) (z : Fin m → ℝ) (S : Finset (Fin m)) :
    (∑ e ∈ insideEdges H S, sqFactor z e) = graphEnergy Hᶜ z S := by
  have he : insideEdges H S = S.sym2.filter fun e => e ∈ Hᶜ.edgeFinset := by
    ext e
    simp [insideEdges, Finset.subset_iff, and_comm]
  rw [he, Finset.sum_filter]
  simp only [graphEnergy, SimpleGraph.mem_edgeFinset]

/-- A product over actual retained inside edges has the usual quadratic
Gaussian majorant whenever the real differences are legally unwrapped. -/
lemma insideProduct_le_energy (H : SimpleGraph (Fin m)) (z : Fin m → ℝ)
    (S : Finset (Fin m))
    (hspan : ∀ i ∈ S, ∀ j ∈ S, |z i-z j| ≤ Real.pi/2) :
    insideProduct H z S ≤ Real.exp (-graphEnergy Hᶜ z S/2) := by
  calc
    insideProduct H z S ≤ ∏ e ∈ insideEdges H S, Real.exp (-(sqFactor z e/2)) := by
      apply Finset.prod_le_prod₀ (fun e _ => edgeFactor_nonneg _ _)
      intro e he
      induction e using Sym2.ind with
      | _ i j =>
        have hs := (Finset.mem_filter.mp he).2
        have hi : i ∈ S := hs (by simp)
        have hj : j ∈ S := hs (by simp)
        exact abs_cos_le_gaussian (hspan i hi j hj)
    _ = Real.exp (-(∑ e ∈ insideEdges H S, sqFactor z e)/2) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_neg_distrib, Finset.sum_div, neg_div]
    _ = Real.exp (-graphEnergy Hᶜ z S/2) := by rw [inside_energy_eq]

/-- Complete actual-graph local Quad+Cos endpoint. The p−4 coefficient is
proved from missing degree≤2; neither energy nor spectral loss is assumed. -/
theorem inside_gaussian_bound (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (z : Fin m → ℝ) (S : Finset (Fin m))
    (hspan : ∀ i ∈ S, ∀ j ∈ S, |z i-z j| ≤ Real.pi/2) :
    insideProduct H z S ≤
      Real.exp (-((S.card : ℝ)-4)/2*varianceOn z S) := by
  apply (insideProduct_le_energy H z S hspan).trans
  apply Real.exp_le_exp.mpr
  have h := retained_energy_lower H hdegree z S
  nlinarith

/-- PointOut with the exact fixed-center representatives and the remaining
cluster Gaussian scale. This theorem contains no integration assertion. -/
theorem outlier_kernel_gaussian (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 64 ≤ m) (x : Fin m → ℝ) (c : ℝ)
    (hf : ((far x c).card : ℝ) < (m:ℝ)/4) :
    kernel H x ≤ Real.exp (-kappa1*(m:ℝ)*(outliers x c).card/2) *
      Real.exp (-(((outer x c).card : ℝ)-4)/2 *
        varianceOn (fun i => repr (x i) c) (outer x c)) := by
  apply (outlier_kernel_bound H hdegree hm x c hf).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [← insideProduct_repr H x c]
  apply inside_gaussian_bound H hdegree
  intro i hi j hj
  have h := (outer_short_arc x c hi hj).1
  linarith [Real.pi_pos]

/-- Q_p= p times centered variance and retained energy ≥(1−4/p)Q_p,
expressed without dividing by p so it also covers empty/small finite sets. -/
theorem local_quadratic_certificate (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (z : Fin m → ℝ) (S : Finset (Fin m)) :
    completeEnergy z S = (S.card : ℝ)*varianceOn z S ∧
    ((S.card : ℝ)-4)*varianceOn z S ≤ graphEnergy Hᶜ z S :=
  ⟨completeEnergy_eq_variance z S, retained_energy_lower H hdegree z S⟩

/-- An actual configuration selects one of sixteen fixed centers and satisfies
one of the two full finite bounds. Neither cardinal estimate is an input. -/
theorem finite_cluster_gaussian (H : SimpleGraph (Fin m))
    (hdegree : ∀ i, H.degree i ≤ 2) (hm : 64 ≤ m) (x : Fin m → ℝ) :
    ∃ j : Fin 16, (m:ℝ)/16 ≤ (core x (center j)).card ∧
      (((m:ℝ)/4 ≤ (far x (center j)).card ∧
        kernel H x ≤ Real.exp (-kappa0*(m:ℝ)^2/128)) ∨
       (((far x (center j)).card : ℝ) < (m:ℝ)/4 ∧
        ((outliers x (center j)).card : ℝ) < (m:ℝ)/4 ∧
        kernel H x ≤ Real.exp (-kappa1*(m:ℝ)*(outliers x (center j)).card/2) *
          Real.exp (-(((outer x (center j)).card : ℝ)-4)/2 *
            varianceOn (fun i => repr (x i) (center j)) (outer x (center j))))) := by
  obtain ⟨j,hj⟩ := exists_large_core x
  refine ⟨j,hj,?_⟩
  by_cases hf : (m:ℝ)/4 ≤ (far x (center j)).card
  · exact Or.inl ⟨hf, far_kernel_bound H hdegree hm x _ hj hf⟩
  · have hf' := lt_of_not_ge hf
    exact Or.inr ⟨hf', outliers_lt_quarter_of_not_far x _ hf',
      outlier_kernel_gaussian H hdegree hm x _ hf'⟩

end
end TorusCluster
