module

public import TournamentHamiltonian.WeightedMotif.Moments

@[expose] public section

set_option autoImplicit false
namespace WeightedMotif
open TournamentHamiltonian TripleContraction UniformDeletion FiniteMotif Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m : ℕ}

def firstMain (d m : ℕ) : ℝ := (Fintype.card (Motif d m) : ℝ)/((m : ℝ)*((d*m : ℕ)-1 : ℝ)^2)
def secondMain (d m : ℕ) : ℝ := (Fintype.card (DisjointPair d m) : ℝ)/((m : ℝ)^2*((d*m : ℕ)-1 : ℝ)^4)

theorem firstMain_eq (d m : ℕ) :
    firstMain d m=(d*m.descFactorial 3 : ℕ)/((m : ℝ)*((d*m : ℕ)-1 : ℝ)^2) := by
  rw [firstMain,card_motif]
theorem secondMain_eq (d m : ℕ) :
    secondMain d m=(d*(d-1)*(m.descFactorial 3)^2+d*m.descFactorial 6 : ℕ)/
      ((m : ℝ)^2*((d*m : ℕ)-1 : ℝ)^4) := by
  rw [secondMain,card_disjoint_pair]

theorem firstMain_nonneg (d m : ℕ) : 0≤firstMain d m := by unfold firstMain; positivity
theorem secondMain_nonneg (d m : ℕ) : 0≤secondMain d m := by unfold secondMain; positivity

theorem cycle_first_error (T : Tournament d) (hm : 0<m) (hN : 2≤d*m) (ε : ℝ)
    (h : ∀ t : Motif d m,|((d*m : ℕ)-1 : ℝ)^2*cycleSingle T t-1|≤ε) :
    |cycleMean (m:=m) T-firstMain d m|≤ε*firstMain d m := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hNR : (1 : ℝ)<(d*m : ℕ) := by exact_mod_cast (show 1<d*m by omega)
  rw [cycle_mean_eq]
  simpa only [firstMain,mul_div_assoc] using
    sum_error (cycleSingle T) m (((d*m : ℕ)-1 : ℝ)^2) ε hmR (sq_pos_of_pos (by linarith)) h

theorem path_first_error (T : Tournament d) (hm : 0<m) (hN : 2≤d*m) (ε : ℝ)
    (h : ∀ t : Motif d m,|((d*m : ℕ)-1 : ℝ)^2*pathSingle T t-1|≤ε) :
    |pathMean (m:=m) T-firstMain d m|≤ε*firstMain d m := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hNR : (1 : ℝ)<(d*m : ℕ) := by exact_mod_cast (show 1<d*m by omega)
  rw [path_mean_eq]
  simpa only [firstMain,mul_div_assoc] using
    sum_error (pathSingle T) m (((d*m : ℕ)-1 : ℝ)^2) ε hmR (sq_pos_of_pos (by linarith)) h

theorem cycle_pair_error (T : Tournament d) (hm : 0<m) (hN : 2≤d*m) (ε : ℝ)
    (h : ∀ p : DisjointPair d m,|((d*m : ℕ)-1 : ℝ)^4*cycleDouble T p-1|≤ε) :
    |cycleDisjoint (m:=m) T-secondMain d m|≤ε*secondMain d m := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hNR : (1 : ℝ)<(d*m : ℕ) := by exact_mod_cast (show 1<d*m by omega)
  rw [cycle_disjoint_eq]
  simpa only [secondMain,mul_div_assoc] using
    sum_error (cycleDouble T) ((m : ℝ)^2) (((d*m : ℕ)-1 : ℝ)^4) ε
      (sq_pos_of_pos hmR) (pow_pos (by linarith) _) h

theorem path_pair_error (T : Tournament d) (hm : 0<m) (hN : 2≤d*m) (ε : ℝ)
    (h : ∀ p : DisjointPair d m,|((d*m : ℕ)-1 : ℝ)^4*pathDouble T p-1|≤ε) :
    |pathDisjoint (m:=m) T-secondMain d m|≤ε*secondMain d m := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hNR : (1 : ℝ)<(d*m : ℕ) := by exact_mod_cast (show 1<d*m by omega)
  rw [path_disjoint_eq]
  simpa only [secondMain,mul_div_assoc] using
    sum_error (pathDouble T) ((m : ℝ)^2) (((d*m : ℕ)-1 : ℝ)^4) ε
      (sq_pos_of_pos hmR) (pow_pos (by linarith) _) h

theorem second_error_of_pair {a b o q e r : ℝ} (ha : a=b+o)
    (hb : |b-q|≤e) (ho : 0≤o) (hor : o≤r) : |a-q|≤e+r := by
  rw [ha,show b+o-q=(b-q)+o by ring]
  exact (abs_add_le _ _).trans (add_le_add hb ((abs_of_nonneg ho).le.trans hor))

/-- Finite inequalities on two actual normalized laws, without any common sample space. -/
structure MomentBounds (T : Tournament d) (m : ℕ) (ε : ℝ) : Prop where
  cyclePositive : 0<total (cycleWeight (m:=m) T)
  pathPositive : 0<total (pathWeight (m:=m) T)
  blockPositive : 0<m
  orderLarge : 6≤d*m
  cycleFirst : |cycleMean (m:=m) T-firstMain d m|≤ε*firstMain d m
  pathFirst : |pathMean (m:=m) T-firstMain d m|≤ε*firstMain d m
  cyclePair : |cycleDisjoint (m:=m) T-secondMain d m|≤ε*secondMain d m
  pathPair : |pathDisjoint (m:=m) T-secondMain d m|≤ε*secondMain d m
  cycleOverlapBound : 0≤cycleOverlap (m:=m) T ∧ cycleOverlap (m:=m) T≤5*(d : ℝ)/m
  pathOverlapBound : 0≤pathOverlap (m:=m) T ∧ pathOverlap (m:=m) T≤5*(d : ℝ)/m
  cycleSquare : |cycleSecond (m:=m) T-secondMain d m|≤ε*secondMain d m+5*(d : ℝ)/m
  pathSquare : |pathSecond (m:=m) T-secondMain d m|≤ε*secondMain d m+5*(d : ℝ)/m

/-- For each ε the common cutoff precedes all motif/pair summations. -/
theorem actual_moment_bounds {d : ℕ} (T : Tournament d)
    (hT : UniformBlockMatrix.IsRegular T) (hd : 0<d) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, MomentBounds T m ε := by
  filter_upwards [actual_event_errors T hT hd ε hε] with m h
  obtain ⟨hC,hH,hN,hs,hp⟩ := h
  have hm : 0<m := by nlinarith
  have hc1 := cycle_first_error T hm (by omega) ε (fun t => (hs t).1.le)
  have hh1 := path_first_error T hm (by omega) ε (fun t => (hs t).2.le)
  have hc2 := cycle_pair_error T hm (by omega) ε (fun p => (hp p).1.le)
  have hh2 := path_pair_error T hm (by omega) ε (fun p => (hp p).2.le)
  have hco := cycle_overlap_bounds T hC hm
  have hho := path_overlap_bounds T hH hm
  exact ⟨hC,hH,hm,hN,hc1,hh1,hc2,hh2,hco,hho,
    second_error_of_pair (cycle_second_partition T) hc2 hco.1 hco.2,
    second_error_of_pair (path_second_partition T) hh2 hho.1 hho.2⟩

end
end WeightedMotif
