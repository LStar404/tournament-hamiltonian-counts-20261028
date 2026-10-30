module

public import TournamentHamiltonian.RegularFourier.Forest

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation UniformBlowup TournamentHamiltonian
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

lemma all_tournaments_card (m : ℕ) : Fintype.card (Tournament m)=2^(Fintype.card (Edge m)) := by
  rw [internal_tournament_card,card_edge]

def containsEquiv {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) :
    {a : Orientation m // ∀e∈s,a e=ω e} ≃ {T : Tournament m // Contains T s ω} where
  toFun a := ⟨internalTournament a.val,(contains_internal_iff _ _ _).mpr a.property⟩
  invFun T := ⟨tournamentBits T.val,(contains_iff_bits _ _ _).mp T.property⟩
  left_inv a := Subtype.ext ((tournamentEquiv m).left_inv a.val)
  right_inv T := Subtype.ext ((tournamentEquiv m).right_inv T.val)

/-- Actual number of independent-bit completions after fixing the prescribed arcs. -/
lemma completions_card {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) :
    (Finset.univ.filter (fun T : Tournament m => Contains T s ω)).card=2^sᶜ.card := by
  have h := Fintype.card_congr (containsEquiv s ω)
  simp only [Fintype.card_subtype] at h
  rw [← h,fixed_filter_card,Finset.card_compl]

lemma regular_count (k : ℕ) :
    (Finset.univ.filter (fun T : Tournament (2*k+1) => IsRegular T)).card=
      (orientationPolynomial (2*k+1)).coeff (regularExponent k) := by
  rw [orientationPolynomial_coeff]
  congr 1
  ext T
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,regular_iff_outVector]

lemma regular_joint_count {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    (Finset.univ.filter (fun T : Tournament (2*k+1) => Contains T s ω ∧ IsRegular T)).card=
      (constrainedPolynomial s ω).coeff (regularExponent k) := by
  rw [constrainedPolynomial_coeff]
  congr 1
  ext T
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,regular_iff_outVector]

def ambientRegularRate (k : ℕ) : ℝ :=
  ((Finset.univ.filter (fun T : Tournament (2*k+1) => IsRegular T)).card : ℝ)/
    Fintype.card (Tournament (2*k+1))
def ambientJointRate {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) : ℝ :=
  ((Finset.univ.filter (fun T : Tournament (2*k+1) => Contains T s ω ∧ IsRegular T)).card : ℝ)/
    Fintype.card (Tournament (2*k+1))
def forcedRegularRate {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) : ℝ :=
  ((Finset.univ.filter (fun T : Tournament (2*k+1) => Contains T s ω ∧ IsRegular T)).card : ℝ)/
    (Finset.univ.filter (fun T : Tournament (2*k+1) => Contains T s ω)).card

lemma ambientRegularRate_integral (k : ℕ) (ω : Orientation (2*k+1)) :
    ambientRegularRate k=(rootIntegral ∅ ω).re/Real.pi^(2*k) := by
  rw [ambientRegularRate,regular_count,all_tournaments_card,Nat.cast_pow,Nat.cast_ofNat]
  exact regular_sample_rate k ω
lemma ambientJointRate_integral {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    ambientJointRate s ω=((2:ℝ)^s.card)⁻¹*(rootIntegral s ω).re/Real.pi^(2*k) := by
  rw [ambientJointRate,regular_joint_count,all_tournaments_card,Nat.cast_pow,Nat.cast_ofNat]
  exact joint_sample_rate s ω
lemma forcedRegularRate_integral {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    forcedRegularRate s ω=(rootIntegral s ω).re/Real.pi^(2*k) := by
  rw [forcedRegularRate,regular_joint_count,completions_card,Nat.cast_pow,Nat.cast_ofNat]
  exact forced_sample_rate s ω

lemma ambientRegularRate_pos (k : ℕ) : 0<ambientRegularRate k := by
  rw [ambientRegularRate,regular_count,all_tournaments_card]
  exact div_pos (regular_denominator_pos k) (by positivity)

/-- Conditional probability on the genuine regular sample space, not the forced-bit space. -/
lemma regularProbability_conditional {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    regularProbability s ω=ambientJointRate s ω/ambientRegularRate k := by
  rw [regularProbability_eq_coeff_ratio,ambientJointRate,ambientRegularRate,
    regular_count,regular_joint_count,all_tournaments_card]
  have hd := (regular_denominator_pos k).ne'
  field_simp

lemma complement_card {m : ℕ} (s : Finset (Edge m)) :
    sᶜ.card=Fintype.card (Edge m)-s.card := Finset.card_compl s

/-- Forest-specialized exact probability bridge using the actual recovered arcs and edge count. -/
theorem forest_regularProbability_integral {k : ℕ} (F : ForestGaussian.EdgeSet (2*k+1)) :
    regularProbability (forestEdges F) (forestOrientation F) =
      ((2:ℝ)^(ForestGaussian.edgeCount F))⁻¹ *
        (rootIntegral (forestEdges F) (forestOrientation F)).re/
          (rootIntegral ∅ (forestOrientation F)).re := by
  rw [regularProbability_integral,forest_edge_count]

end RegularFourier
