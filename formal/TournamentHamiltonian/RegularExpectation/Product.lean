module

public import TournamentHamiltonian.BlockMotif.Endpoint
public import TournamentHamiltonian.RegularContainment.Endpoint

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RegularExpectation
open BlockMotif ForestGaussian RegularOrientation RegularFourier TournamentHamiltonian
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A single tolerance works for every positive main-term vector. Only the finite
number d of coordinates enters; no candidate-dependent threshold is chosen. -/
theorem product_relative_tolerance (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃η : ℝ,0<η ∧ ∀p q : Fin d → ℝ,(∀b,0<q b) →
      (∀b,|p b/q b-1|≤η) → |(∏b,p b)-(∏b,q b)|≤ε*(∏b,q b) := by
  have hcont : Continuous (fun x : Fin d → ℝ => ∏b,x b) :=
    continuous_finsetProd _ (fun b _ => continuous_apply b)
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x:=fun _ => 1)) ε hε
  refine ⟨δ/2,by positivity,?_⟩
  intro p q hq hp
  have hdist : dist (fun b => p b/q b) (fun _ : Fin d => (1:ℝ))<δ := by
    apply (dist_pi_lt_iff hδ).mpr
    intro b
    rw [Real.dist_eq]
    exact (hp b).trans_lt (by linarith)
  have h := hd hdist
  simp only [Real.dist_eq,Finset.prod_const_one,Finset.prod_div_distrib] at h
  have hQ : 0<∏b,q b := Finset.prod_pos (fun b _ => hq b)
  have he : (∏b,p b)/(∏b,q b)-1=((∏b,p b)-(∏b,q b))/(∏b,q b) := by
    field_simp
  rw [he,abs_div,abs_of_pos hQ] at h
  exact ((div_lt_iff₀ hQ).mp h).le

/-- The original containment theorem supplies one threshold before *all* actual
EdgeSets, hence before all base tournaments and all Hamilton candidates. -/
theorem candidate_error_threshold (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃M : ℕ,∀k : ℕ,M≤2*k+1 → ∀T : Tournament d,
      ∀R : ArcSystem (Fin (d*(2*k+1))),
        |regularCandidateProbability R T-
            (if CrossCompatible R T then (1:ℝ) else 0)*(∏b,blockApprox (blockSet R b))|≤
          ε*((if CrossCompatible R T then (1:ℝ) else 0)*(∏b,blockApprox (blockSet R b))) := by
  obtain ⟨η,hη,hprod⟩ := product_relative_tolerance d ε hε
  obtain ⟨M,hM⟩ := RegularContainment.uniform_regularProbability η hη
  refine ⟨M,fun k hk T R => ?_⟩
  rw [regularCandidate_product]
  by_cases hc : CrossCompatible R T
  · simp only [hc,ite_true,one_mul]
    apply hprod _ _ (fun b => blockApprox_pos _)
    intro b
    simpa only [blockApprox_eq,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hM k hk (blockSet R b)
  · simp only [hc,ite_false,zero_mul,mul_zero,sub_self,abs_zero,le_refl]

end
end RegularExpectation
