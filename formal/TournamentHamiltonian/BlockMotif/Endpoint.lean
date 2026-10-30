module

public import TournamentHamiltonian.BlockMotif.Weights
public import TournamentHamiltonian.BlockMotif.Native

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BlockMotif
open TripleContraction FiniteMotif ForestGaussian TournamentHamiltonian
open RegularOrientation RegularFourier UniformBlowup
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m k : ℕ}

theorem regular_uniform_mass_sum (d k : ℕ) :
    (∑_ω : RegularSample d k,(1:ℝ)/Fintype.card (RegularSample d k))=1 := by
  have h := ne_of_gt (regularCandidate_denominator_pos d k)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one_div,div_self h]

theorem regularCandidate_bounds (R : ArcSystem (Fin (d*(2*k+1)))) (T : Tournament d) :
    0≤regularCandidateProbability R T ∧ regularCandidateProbability R T≤1 := by
  have hz := regularCandidate_denominator_pos d k
  refine ⟨div_nonneg (Finset.sum_nonneg (by intro ω _; split_ifs <;> norm_num)) hz.le,?_⟩
  apply (div_le_iff₀ hz).mpr
  calc
    ∑ω : RegularSample d k, (if Contained R (regularBlowup T ω finProdFinEquiv.symm) then (1:ℝ) else 0)
        ≤ ∑_ω : RegularSample d k,(1:ℝ) := Finset.sum_le_sum (by intro ω _; split_ifs <;> norm_num)
    _ = _ := by simp

/-- Exact finite average over the old actual unrooted-cycle predicate. -/
theorem regular_cycle_product (hN : 3≤d*(2*k+1)) (σ : Full (Fin (d*(2*k+1)))) (T : Tournament d) :
    (∑ω : RegularSample d k,if IsCyclePresent T (regularSampleBits ω) (nativeCycle hN σ) then (1:ℝ) else 0)/
        Fintype.card (RegularSample d k)=
      (if CrossCompatible (cycleSystem hN σ) T then (1:ℝ) else 0)*
        ∏b,regularProbability (forestEdges (blockSet (cycleSystem hN σ) b))
          (forestOrientation (blockSet (cycleSystem hN σ) b)) := by
  simpa only [regularCandidateProbability,regular_cycle_native] using regularCandidate_product (cycleSystem hN σ) T

/-- Exact finite average over the old actual non-wrapping-path predicate. -/
theorem regular_path_product (π : Ordering (Fin (d*(2*k+1)))) (T : Tournament d) :
    (∑ω : RegularSample d k,if IsPath T (regularSampleBits ω) (nativeArrangement π) then (1:ℝ) else 0)/
        Fintype.card (RegularSample d k)=
      (if CrossCompatible (pathSystem π) T then (1:ℝ) else 0)*
        ∏b,regularProbability (forestEdges (blockSet (pathSystem π) b))
          (forestOrientation (blockSet (pathSystem π) b)) := by
  simpa only [regularCandidateProbability,regular_path_native] using regularCandidate_product (pathSystem π) T

theorem cycle_weight_blocks (hN : 3≤d*m) (σ : Full (Fin (d*m))) (T : Tournament d) :
    monomial (UniformDeletion.weightFin T) σ.val=
      (if CrossCompatible (cycleSystem hN σ) T then (1:ℝ) else 0)*
        (1/2:ℝ)^(∑b,edgeCount (blockSet (cycleSystem hN σ) b)) := by
  rw [cycle_monomial_arcs hN,arcProduct_uniform]

theorem path_weight_blocks (π : Ordering (Fin (d*m))) (T : Tournament d) :
    pathMonomial (UniformDeletion.weightFin T) π=
      (if CrossCompatible (pathSystem π) T then (1:ℝ) else 0)*
        (1/2:ℝ)^(∑b,edgeCount (blockSet (pathSystem π) b)) := by
  rw [path_monomial_arcs,arcProduct_uniform]

/-- The integer source correction agrees with the real-valued exponent of the
regular-containment endpoint. -/
theorem sum_real_edge_sub_source (R : ArcSystem (Fin (d*m))) :
    (∑b,((edgeCount (blockSet R b):ℝ)-sourceCount (blockSet R b)))=(present R).card := by
  have hle (b : Fin d) : sourceCount (blockSet R b)≤edgeCount (blockSet R b) := by
    rw [edgeCount_eq_source_add_middle]; omega
  simp_rw [←Nat.cast_sub (hle _)]
  rw [←Nat.cast_sum,sum_edge_sub_source]

def blockApprox (F : EdgeSet m) : ℝ :=
  (1/2:ℝ)^(edgeCount F)*Real.exp (((edgeCount F:ℝ)-sourceCount F)/m)

/-- Exactly the denominator used by `RegularContainment.uniform_regularProbability`. -/
theorem blockApprox_eq (F : EdgeSet m) : blockApprox F=
    ((2:ℝ)^(edgeCount F))⁻¹*Real.exp (((edgeCount F:ℝ)-sourceCount F)/m) := by
  simp only [blockApprox,one_div,inv_pow]

theorem blockApprox_pos (F : EdgeSet m) : 0<blockApprox F := by
  unfold blockApprox
  positivity

theorem blockApprox_product (R : ArcSystem (Fin (d*m))) :
    (∏b,blockApprox (blockSet R b))=
      (1/2:ℝ)^(∑b,edgeCount (blockSet R b))*Real.exp (((present R).card:ℝ)/m) := by
  simp only [blockApprox,Finset.prod_mul_distrib]
  rw [←Finset.prod_pow_eq_pow_sum,←Real.exp_sum,←Finset.sum_div,sum_real_edge_sub_source]

theorem cycle_correction_product (hN : 3≤d*m) (σ : Full (Fin (d*m))) (T : Tournament d) :
    (if CrossCompatible (cycleSystem hN σ) T then (1:ℝ) else 0)*
        (∏b,blockApprox (blockSet (cycleSystem hN σ) b))=
      monomial (UniformDeletion.weightFin T) σ.val*Real.exp ((cycleA σ:ℝ)/m) := by
  rw [blockApprox_product,cycle_weight_blocks]
  have ha : (present (cycleSystem hN σ)).card=cycleA σ := by
    rw [←sum_edge_sub_source,cycle_a_sub_s]
  rw [ha,mul_assoc]

theorem path_correction_product (π : Ordering (Fin (d*m))) (T : Tournament d) :
    (if CrossCompatible (pathSystem π) T then (1:ℝ) else 0)*
        (∏b,blockApprox (blockSet (pathSystem π) b))=
      pathMonomial (UniformDeletion.weightFin T) π*Real.exp ((pathA π:ℝ)/m) := by
  rw [blockApprox_product,path_weight_blocks]
  have ha : (present (pathSystem π)).card=pathA π := by
    rw [←sum_edge_sub_source,path_a_sub_s]
  rw [ha,mul_assoc]

end
end BlockMotif
