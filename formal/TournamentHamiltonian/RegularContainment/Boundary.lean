module

public import TournamentHamiltonian.RegularContainment.Endpoint
public import TournamentHamiltonian.RootGaussianTail.Boundary

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularContainment
open Matrix MeasureTheory ForestGaussian ForestGaussianIntegral PDGaussian RootGaussianTail Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

lemma one_vertex_integral : torusIntegral (emptyEdgeSet 1) = 1 :=
  RegularFourier.order_one_root _ _

lemma one_vertex_normalizer : Z 1 1=1 := partition_empty_dimension 1 (by norm_num)

lemma empty_regularProbability (k : ℕ) :
    RegularOrientation.regularProbability (RegularFourier.forestEdges (emptyEdgeSet (2*k+1)))
      (RegularFourier.forestOrientation (emptyEdgeSet (2*k+1))) = 1 := by
  rw [RegularFourier.forest_regularProbability_integral]
  have he : RegularFourier.forestEdges (emptyEdgeSet (2*k+1))=∅ := by
    simp [RegularFourier.forestEdges, emptyEdgeSet_graph]
  have ha : edgeCount (emptyEdgeSet (2*k+1))=0 := by simp [edgeCount,emptyEdgeSet]
  rw [ha, pow_zero, inv_one, one_mul, he]
  exact div_self (RegularFourier.empty_rootIntegral_pos k _).ne'

lemma empty_target_ratio (k : ℕ) :
    RegularOrientation.regularProbability (RegularFourier.forestEdges (emptyEdgeSet (2*k+1)))
      (RegularFourier.forestOrientation (emptyEdgeSet (2*k+1))) /
      (((2:ℝ)^edgeCount (emptyEdgeSet (2*k+1)))⁻¹ *
        Real.exp (((edgeCount (emptyEdgeSet (2*k+1)):ℝ)-sourceCount (emptyEdgeSet (2*k+1)))/(2*k+1))) = 1 := by
  rw [empty_regularProbability]
  simp [edgeCount, sourceCount, emptyEdgeSet, outCount, inCount]

/-- The zero-probability m=3 fork from E is not accidentally in the theorem's domain. -/
lemma fork_three_not_EdgeSet :
    ¬∃ F : EdgeSet 3, F.edges = {((0:Fin 3),1),(0,2)} := by
  rintro ⟨F,hF⟩
  have h := F.out_le_one 0
  rw [hF] at h
  exact (by decide : ¬outCount ({((0:Fin 3),1),(0,2)} : Finset (Fin 3 × Fin 3)) 0 ≤ 1) h

/-- Directed cycles are nevertheless genuinely allowed by EdgeSet. -/
def cycleThree : EdgeSet 3 where
  edges := {((0:Fin 3),1),(1,2),(2,0)}
  loopless := by decide
  no_reverse := by decide
  out_le_one := by decide
  in_le_one := by decide

lemma cycleThree_counts : edgeCount cycleThree=3 ∧ sourceCount cycleThree=0 := by
  norm_num [edgeCount,sourceCount,cycleThree,outCount,inCount,Fin.sum_univ_succ]
  decide

lemma loops_excluded {m : ℕ} (F : EdgeSet m) (i : Fin m) : (i,i)∉F.edges := F.loopless i
lemma reversals_excluded {m : ℕ} (F : EdgeSet m) (i j : Fin m) (h : (i,j)∈F.edges) :
    (j,i)∉F.edges := F.no_reverse i j h

/-- The factor 4 and the subsequent factor 3 are both attained at κ=1/2. -/
lemma quotient_constants_attained (ε : ℝ) (hε : 0 ≤ ε) :
    |((3:ℝ)/2)/((1:ℝ)/2)*(1+ε)-1| = 4*((1:ℝ)/2)+3*ε := by
  norm_num
  rw [abs_of_nonneg (by linarith)]
  ring

lemma two_vertex_real_kernel (x : Fin 1 → ℝ) :
    realKernel (rootMatrix (emptyEdgeSet 2)) 0 x = Real.exp (-(x 0)^2/2) := by
  rw [completeRoot_empty]
  have h := density_one_dimension 1 x
  simpa only [density, one_smul, neg_one_mul] using h

lemma order_two_signed_gauge_counterexample :
    (∫ x, RegularFourier.signedKernel ∅ (fun _ => false) x ∂PeriodicBox.boxMeasure 2 (-Real.pi/2)) ≠
      (Real.pi:ℂ)*RegularFourier.rootIntegral ∅ (fun _ : UniformBlowup.Edge 2 => false) :=
  RegularFourier.order_two_gauge_fails _

end RegularContainment
