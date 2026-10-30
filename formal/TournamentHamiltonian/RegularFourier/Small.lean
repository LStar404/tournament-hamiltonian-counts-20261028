module

public import TournamentHamiltonian.RegularFourier.Boundary

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation UniformBlowup
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def forwardThree : Orientation 3 := fun _ => true
def singleThree : Finset (Edge 3) := {e01}
def pathThree : Finset (Edge 3) := {e01,e12}
def forkThree : Finset (Edge 3) := {e01,e02}

lemma regular_coeff_three : (orientationPolynomial 3).coeff (regularExponent 1)=2 := by
  simp [orientationPolynomial,edge_univ_three,e01,e02,e12,X,mul_add,add_mul,
    regularExponent,Finsupp.ext_iff,Fin.forall_fin_succ]
lemma single_coeff_three : (constrainedPolynomial singleThree forwardThree).coeff (regularExponent 1)=1 := by
  simp [constrainedPolynomial,singleThree,forwardThree,edge_univ_three,e01,e02,e12,winner,
    X,mul_add,add_mul,regularExponent,Finsupp.ext_iff,Fin.forall_fin_succ]
lemma path_coeff_three : (constrainedPolynomial pathThree forwardThree).coeff (regularExponent 1)=1 := by
  simp [constrainedPolynomial,pathThree,forwardThree,edge_univ_three,e01,e02,e12,winner,
    X,mul_add,add_mul,regularExponent,Finsupp.ext_iff,Fin.forall_fin_succ]
lemma fork_coeff_three : (constrainedPolynomial forkThree forwardThree).coeff (regularExponent 1)=0 := by
  simp [constrainedPolynomial,forkThree,forwardThree,edge_univ_three,e01,e02,e12,winner,
    X,mul_add,regularExponent,Finsupp.ext_iff,Fin.forall_fin_succ]

lemma path_imbalance_three : imbalance pathThree forwardThree=![1,0,-1] := by
  ext i
  fin_cases i <;> norm_num [imbalance,pathThree,forwardThree,winner,loser,e01,e12,Finset.sum_insert,Finset.sum_singleton,Finset.filter_insert,Finset.filter_singleton]
lemma fork_imbalance_three : imbalance forkThree forwardThree=![2,-1,-1] := by
  ext i
  fin_cases i <;> norm_num [imbalance,forkThree,forwardThree,winner,loser,e01,e02,Finset.sum_insert,Finset.sum_singleton,Finset.filter_insert,Finset.filter_singleton]

lemma empty_integral_three : rootIntegral ∅ forwardThree=(Real.pi^2/4:ℝ) := by
  rw [rootIntegral_eq_real (k:=1),constrained_empty,regular_coeff_three]
  norm_num [Finset.card_compl,card_edge]
  ring
lemma path_integral_three : rootIntegral pathThree forwardThree=(Real.pi^2/2:ℝ) := by
  rw [rootIntegral_eq_real (k:=1),path_coeff_three]
  norm_num [Finset.card_compl,card_edge,pathThree,e01,e12]
lemma fork_integral_three : rootIntegral forkThree forwardThree=0 := by
  rw [rootIntegral_eq_real (k:=1),fork_coeff_three]
  simp
lemma single_probability_three : regularProbability (k:=1) singleThree forwardThree=1/2 := by
  rw [regularProbability_eq_coeff_ratio,single_coeff_three,regular_coeff_three]
  norm_num
lemma path_probability_three : regularProbability (k:=1) pathThree forwardThree=1/2 := by
  rw [regularProbability_eq_coeff_ratio,path_coeff_three,regular_coeff_three]
  norm_num
lemma fork_probability_three : regularProbability (k:=1) forkThree forwardThree=0 := by
  rw [regularProbability_eq_coeff_ratio,fork_coeff_three,regular_coeff_three]
  norm_num
lemma regular_rate_three : ambientRegularRate 1=1/4 := by
  rw [ambientRegularRate,regular_count,regular_coeff_three,internal_tournament_card]
  norm_num
lemma path_joint_rate_three : ambientJointRate (k:=1) pathThree forwardThree=1/8 := by
  rw [ambientJointRate,regular_joint_count,path_coeff_three,internal_tournament_card]
  norm_num
lemma path_forced_rate_three : forcedRegularRate (k:=1) pathThree forwardThree=1/2 := by
  rw [forcedRegularRate,regular_joint_count,path_coeff_three,completions_card]
  norm_num [Finset.card_compl,card_edge,pathThree,e01,e12]

end RegularFourier
