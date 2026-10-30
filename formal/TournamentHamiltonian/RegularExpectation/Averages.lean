module

public import TournamentHamiltonian.RegularExpectation.Product
public import TournamentHamiltonian.MotifExp.Endpoint
public import TournamentHamiltonian.NonregularDecay.ExpectationDecay

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RegularExpectation
open BlockMotif TripleContraction FiniteMotif TournamentHamiltonian UniformBlowup RegularOrientation NonregularDecay
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m k : ℕ}

theorem regular_path_sum (T : Tournament d) (k : ℕ) :
    regularAvgPath T k=∑π : Ordering (Fin (d*(2*k+1))),regularCandidateProbability (pathSystem π) T := by
  have hω (ω : RegularSample d k) :
      (UniformBlowup.pathCount T (regularSampleBits ω):ℝ)=
        ∑π : Ordering (Fin (d*(2*k+1))),
          if Contained (pathSystem π) (regularBlowup T ω finProdFinEquiv.symm) then (1:ℝ) else 0 := by
    simp only [UniformBlowup.pathCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    symm
    apply Fintype.sum_equiv nativeArrangementEquiv
    intro π
    simp only [nativeArrangementEquiv_apply,regular_path_native]
  simp only [regularAvgPath,hω]
  rw [Finset.sum_comm,Finset.sum_div]
  rfl

theorem regular_cycle_sum (T : Tournament d) (k : ℕ) (hN : 3≤d*(2*k+1)) :
    regularAvgCycle T k=∑σ : Full (Fin (d*(2*k+1))),regularCandidateProbability (cycleSystem hN σ) T := by
  have hω (ω : RegularSample d k) :
      (UniformBlowup.cycleCount T (regularSampleBits ω):ℝ)=
        ∑σ : Full (Fin (d*(2*k+1))),
          if Contained (cycleSystem hN σ) (regularBlowup T ω finProdFinEquiv.symm) then (1:ℝ) else 0 := by
    simp only [UniformBlowup.cycleCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    symm
    apply Fintype.sum_equiv (nativeCycleEquiv hN)
    intro σ
    simp only [nativeCycleEquiv_apply,regular_cycle_native]
  simp only [regularAvgCycle,hω]
  rw [Finset.sum_comm,Finset.sum_div]
  rfl

def cycleCorrected (T : Tournament d) (m : ℕ) : ℝ :=
  ∑σ : Full (Fin (d*m)),WeightedMotif.cycleWeight T σ*Real.exp ((cycleA σ:ℝ)/m)
def pathCorrected (T : Tournament d) (m : ℕ) : ℝ :=
  ∑π : Ordering (Fin (d*m)),WeightedMotif.pathWeight T π*Real.exp ((pathA π:ℝ)/m)

theorem cycleCorrected_nonneg (T : Tournament d) (m : ℕ) : 0≤cycleCorrected T m := by
  apply Finset.sum_nonneg
  intro σ _
  exact mul_nonneg (WeightedMotif.cycleWeight_nonneg T σ) (Real.exp_pos _).le

theorem pathCorrected_nonneg (T : Tournament d) (m : ℕ) : 0≤pathCorrected T m := by
  apply Finset.sum_nonneg
  intro π _
  exact mul_nonneg (WeightedMotif.pathWeight_nonneg T π) (Real.exp_pos _).le

theorem sum_mul_expect {α : Type*} [Fintype α] (w f : α → ℝ) (hZ : WeightedMotif.total w≠0) :
    (∑x,w x*f x)=WeightedMotif.total w*WeightedMotif.expect w f := by
  simp only [WeightedMotif.expect,WeightedMotif.mass,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp

theorem cycle_total_uniform (T : Tournament d) (hN : 3≤d*m) :
    WeightedMotif.total (WeightedMotif.cycleWeight (m:=m) T)=avgCycle (m:=m) T := by
  let : Nonempty (Fin (d*m)) := ⟨⟨0,by omega⟩⟩
  rw [WeightedMotif.cycle_total,UniformDeletion.weightFin,
    UniformFinalScalars.cyc_submatrix_equiv,WeightedCycle.cyc_eq_uniform_weightedCycleSum (by omega),
    avgCycle_eq_weightedCycleSum hN]

theorem path_total_uniform (T : Tournament d) :
    WeightedMotif.total (WeightedMotif.pathWeight (m:=m) T)=avgPath (m:=m) T := by
  rw [WeightedMotif.path_total,UniformDeletion.weightFin,
    UniformFinalScalars.path_submatrix_equiv,WeightedCycle.path_eq_uniform_avgPath]

theorem cycleCorrected_eq (T : Tournament d) (hN : 3≤d*m)
    (hZ : 0<WeightedMotif.total (WeightedMotif.cycleWeight (m:=m) T)) :
    cycleCorrected T m=avgCycle (m:=m) T*MotifExp.cycleExp (m:=m) T := by
  rw [cycleCorrected,sum_mul_expect _ _ hZ.ne',cycle_total_uniform T hN]
  rfl

theorem pathCorrected_eq (T : Tournament d)
    (hZ : 0<WeightedMotif.total (WeightedMotif.pathWeight (m:=m) T)) :
    pathCorrected T m=avgPath (m:=m) T*MotifExp.pathExp (m:=m) T := by
  rw [pathCorrected,sum_mul_expect _ _ hZ.ne',path_total_uniform T]
  rfl

/-- Finite summation never divides by a candidate probability or its weight. -/
theorem sum_error {α : Type*} [Fintype α] (p q : α → ℝ) (ε : ℝ)
    (h : ∀x,|p x-q x|≤ε*q x) : |(∑x,p x)-(∑x,q x)|≤ε*(∑x,q x) := by
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => h x))

/-- One threshold works simultaneously for all actual paths and unrooted cycles. -/
theorem actual_error_threshold (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃M : ℕ,∀k : ℕ,M≤2*k+1 → ∀T : Tournament d,
      |regularAvgPath T k-pathCorrected T (2*k+1)|≤ε*pathCorrected T (2*k+1) ∧
      (3≤d*(2*k+1) → |regularAvgCycle T k-cycleCorrected T (2*k+1)|≤ε*cycleCorrected T (2*k+1)) := by
  obtain ⟨M,hM⟩ := candidate_error_threshold d ε hε
  refine ⟨M,fun k hk T => ⟨?_,fun hN => ?_⟩⟩
  · rw [regular_path_sum]
    apply sum_error
    intro π
    have h := hM k hk T (pathSystem π)
    rwa [path_correction_product] at h
  · rw [regular_cycle_sum T k hN]
    apply sum_error
    intro σ
    have h := hM k hk T (cycleSystem hN σ)
    rwa [cycle_correction_product] at h

end
end RegularExpectation
