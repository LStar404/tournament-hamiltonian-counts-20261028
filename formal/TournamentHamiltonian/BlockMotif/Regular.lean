module

public import TournamentHamiltonian.BlockMotif.Actual
public import TournamentHamiltonian.RegularOrientation.Blowup
public import TournamentHamiltonian.RegularFourier.Forest

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BlockMotif
open TripleContraction FiniteMotif ForestGaussian TournamentHamiltonian
open RegularOrientation RegularFourier
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {d m k : ℕ}

def Contained (R : ArcSystem (Fin (d*m))) (S : Tournament (d*m)) : Prop :=
  ∀u v,R.rel u v → S.val u v=true

def CrossCompatible (R : ArcSystem (Fin (d*m))) (T : Tournament d) : Prop :=
  ∀u v,R.rel u v → block u≠block v → T.val (block u) (block v)=true

def blockContained (R : ArcSystem (Fin (d*m))) (b : Fin d) (S : Tournament m) : Prop :=
  RegularOrientation.Contains S (forestEdges (blockSet R b)) (forestOrientation (blockSet R b))

theorem blockContained_iff (R : ArcSystem (Fin (d*m))) (b : Fin d) (S : Tournament m) :
    blockContained R b S ↔ ∀i j,R.rel (encode b i) (encode b j) → S.val i j=true := by
  rw [blockContained,forest_contains]
  simp only [blockSet,mem_blockEdges,Prod.forall]

theorem regular_arc (T : Tournament d) (ω : RegularSample d k) (u v : Fin (d*(2*k+1))) :
    (regularBlowup T ω finProdFinEquiv.symm).val u v=
      if block u=block v then (ω (block u)).val.val
        (finProdFinEquiv.symm u).2 (finProdFinEquiv.symm v).2 else T.val (block u) (block v) := by
  change UniformBlowup.arc T (regularSampleBits ω) (finProdFinEquiv.symm u) (finProdFinEquiv.symm v)=_
  by_cases h : block u=block v
  · rw [ite_eq_left h]
    have he : finProdFinEquiv.symm u=(block u,(finProdFinEquiv.symm u).2) := rfl
    have hf : finProdFinEquiv.symm v=(block u,(finProdFinEquiv.symm v).2) := by
      apply Prod.ext
      · exact h.symm
      · rfl
    rw [he,hf,regular_internal_arc]
  · rw [ite_eq_right h]
    exact ite_eq_right h

/-- Exact candidate containment in the actual regular blowup: only blocks are
independent; no statement of independence of edges inside a block is used. -/
theorem regular_contained_iff (R : ArcSystem (Fin (d*(2*k+1))))
    (T : Tournament d) (ω : RegularSample d k) :
    Contained R (regularBlowup T ω finProdFinEquiv.symm) ↔
      CrossCompatible R T ∧ ∀b,blockContained R b (ω b).val := by
  constructor
  · intro h
    constructor
    · intro u v huv hne
      have hh := h u v huv
      rwa [regular_arc,ite_eq_right hne] at hh
    · intro b
      rw [blockContained_iff]
      intro i j hij
      have hh := h (encode b i) (encode b j) hij
      simpa only [regular_arc,encode,block,Equiv.symm_apply_apply,ite_true] using hh
  · rintro ⟨hc,hb⟩ u v huv
    rw [regular_arc]
    split_ifs with he
    · have h := (blockContained_iff R (block u) (ω (block u)).val).mp (hb (block u))
        (finProdFinEquiv.symm u).2 (finProdFinEquiv.symm v).2
      apply h
      have eu : encode (block u) (finProdFinEquiv.symm u).2=u := finProdFinEquiv.apply_symm_apply u
      have ev : encode (block u) (finProdFinEquiv.symm v).2=v := by
        rw [he]; exact finProdFinEquiv.apply_symm_apply v
      rwa [eu,ev]
    · exact hc u v huv he

def regularCandidateProbability (R : ArcSystem (Fin (d*(2*k+1)))) (T : Tournament d) : ℝ :=
  (∑ω : RegularSample d k, if Contained R (regularBlowup T ω finProdFinEquiv.symm) then (1:ℝ) else 0)/
    Fintype.card (RegularSample d k)

theorem regularCandidate_denominator_pos (d k : ℕ) :
    (0:ℝ)<Fintype.card (RegularSample d k) := by exact_mod_cast regularSample_card_pos d k

theorem indicator_forall_product {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] [Decidable (∀i,P i)] :
    (if ∀i,P i then (1:ℝ) else 0)=∏i,if P i then 1 else 0 := by
  by_cases h : ∀i,P i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

theorem regularCandidate_product (R : ArcSystem (Fin (d*(2*k+1)))) (T : Tournament d) :
    regularCandidateProbability R T=
      (if CrossCompatible R T then (1:ℝ) else 0)*
        ∏b,regularProbability (forestEdges (blockSet R b)) (forestOrientation (blockSet R b)) := by
  unfold regularCandidateProbability
  simp_rw [regular_contained_iff]
  by_cases hc : CrossCompatible R T
  · simp only [hc,true_and,ite_true,one_mul]
    simp_rw [indicator_forall_product]
    rw [←Fintype.prod_sum (fun b (S : RegularTournament (2*k+1)) => if blockContained R b S.val then (1:ℝ) else 0)]
    simp only [RegularSample,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
    have hp : (∏_ : Fin d,(Fintype.card (RegularTournament (2*k+1)):ℝ))=(Fintype.card (RegularTournament (2*k+1)):ℝ)^d := by simp
    rw [←hp,←Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro b _
    congr 1
    simp only [blockContained,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  · simp [hc]

end
end BlockMotif
