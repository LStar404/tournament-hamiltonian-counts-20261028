module

public import TournamentHamiltonian.RegularFourier.Small

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation UniformBlowup
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

lemma edge_product {m : ℕ} (f : Fin m → Fin m → ℂ) :
    (∏ e : Edge m,f e.val.1 e.val.2)=∏ i,∏ j,if i < j then f i j else 1 := by
  rw [← Finset.prod_subtype (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2))
    (by simp) (fun p => f p.1 p.2)]
  simp only [Finset.prod_filter]
  exact Fintype.prod_prod_type _

lemma retained_product {m : ℕ} (s : Finset (Edge m)) (x : Fin m → ℝ) :
    (∏ e∈sᶜ,(Real.cos (x e.val.1-x e.val.2):ℂ))=
      ∏ i,∏ j,if i < j ∧ ¬(selectedGraph s).Adj i j then (Real.cos (x i-x j):ℂ) else 1 := by
  have hprod : (∏ e∈sᶜ,(Real.cos (x e.val.1-x e.val.2):ℂ))=
      ∏ e : Edge m,if (selectedGraph s).Adj e.val.1 e.val.2 then 1 else (Real.cos (x e.val.1-x e.val.2):ℂ) := by
    simp_rw [selectedGraph_edge]
    rw [Finset.prod_ite]
    have hs : Finset.univ.filter (fun e : Edge m => e∈s)=s := by ext; simp
    have hc : Finset.univ.filter (fun e : Edge m => e∉s)=sᶜ := by ext; simp
    rw [hs,hc,Finset.prod_const_one,one_mul]
  rw [hprod,edge_product (fun i j => if (selectedGraph s).Adj i j then 1 else (Real.cos (x i-x j):ℂ))]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : i < j <;> by_cases hg : (selectedGraph s).Adj i j <;> simp [h,hg]

/-- The signed kernel in the precise graph/imbalance coordinates of the frozen
Gaussian package. Its phase has the plus sign dictated by forced winner factors. -/
theorem forest_signedKernel {m : ℕ} (F : ForestGaussian.EdgeSet m) (x : Fin m → ℝ) :
    signedKernel (forestEdges F) (forestOrientation F) x =
      Complex.exp ((∑ i,ForestGaussian.imbalance F i*x i : ℝ)*Complex.I)*
        ∏ i,∏ j,if i < j ∧ ¬(ForestGaussian.graph F).Adj i j then (Real.cos (x i-x j):ℂ) else 1 := by
  rw [signedKernel_phase,retained_product,forest_graph]
  simp_rw [forest_imbalance]
  rfl

theorem signed_full_root {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    (∫ x,signedKernel s ω x ∂boxMeasure (2*k+1) (-Real.pi/2))=
      (Real.pi:ℂ)*rootIntegral s ω :=
  complex_gauge _ _ (signedKernel_continuous s ω).measurable (signedKernel_norm_le s ω)
    (signedKernel_periodic s ω) (signedKernel_joint s ω)

/-- Coefficient extraction directly on the ordinary closed root box. -/
theorem coefficient_closed_root {k : ℕ} (s : Finset (Edge (2*k+1))) (ω : Orientation (2*k+1)) :
    ((constrainedPolynomial s ω).coeff (regularExponent k) : ℂ)=
      ((2:ℂ)^(Fintype.card (Edge (2*k+1))-s.card)/(Real.pi:ℂ)^(2*k))*
        ∫ z in univ.pi (fun _ : Fin (2*k) => Icc (-Real.pi/2) (Real.pi/2)),
          signedKernel s ω (Fin.cons 0 z) := by
  rw [← rootIntegral_closed,← Finset.card_compl]
  have h := coefficient_root_integral s ω
  have hp : (Real.pi:ℂ)^(2*k) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hp).mpr h.symm

lemma all_forced_polynomial {m : ℕ} (ω : Orientation m) :
    constrainedPolynomial Finset.univ ω=monomial (winnerExponent ω) 1 := by
  simp only [constrainedPolynomial,Finset.mem_univ,ite_true]
  exact prod_winner_X ω
lemma all_forced_coefficient {k : ℕ} (ω : Orientation (2*k+1)) :
    (constrainedPolynomial Finset.univ ω).coeff (regularExponent k)=
      if winnerExponent ω=regularExponent k then 1 else 0 := by
  rw [all_forced_polynomial,coeff_monomial]
lemma all_forced_root {k : ℕ} (ω : Orientation (2*k+1)) :
    rootIntegral Finset.univ ω =
      if winnerExponent ω=regularExponent k then (Real.pi:ℂ)^(2*k) else 0 := by
  rw [rootIntegral_eq_real,all_forced_coefficient]
  split_ifs <;> simp

lemma empty_signedKernel {m : ℕ} (ω : Orientation m) (x : Fin m → ℝ) :
    signedKernel ∅ ω x=∏ i,∏ j,if i < j then (Real.cos (x i-x j):ℂ) else 1 := by
  simp only [signedKernel,signedFactor,Finset.notMem_empty,ite_false]
  exact edge_product (fun i j => (Real.cos (x i-x j):ℂ))

/-- Literal finite Fourier bridge for the Gaussian package's actual directed arcs.
All measures are ordinary restricted volume, and both root boxes have dimension 2k. -/
theorem forest_regularProbability_closed {k : ℕ} (F : ForestGaussian.EdgeSet (2*k+1)) :
    regularProbability (forestEdges F) (forestOrientation F)=
      ((2:ℝ)^(ForestGaussian.edgeCount F))⁻¹ *
        (∫ z in univ.pi (fun _ : Fin (2*k) => Icc (-Real.pi/2) (Real.pi/2)),
          Complex.exp ((∑ i,ForestGaussian.imbalance F i*(Fin.cons (0:ℝ) z : Fin (2*k+1) → ℝ) i : ℝ)*Complex.I)*
            ∏ i,∏ j,if i < j ∧ ¬(ForestGaussian.graph F).Adj i j then
              (Real.cos ((Fin.cons (0:ℝ) z : Fin (2*k+1) → ℝ) i-(Fin.cons (0:ℝ) z : Fin (2*k+1) → ℝ) j):ℂ) else 1).re /
        (∫ z in univ.pi (fun _ : Fin (2*k) => Icc (-Real.pi/2) (Real.pi/2)),
          ∏ i : Fin (2*k+1),∏ j : Fin (2*k+1),if i < j then
            (Real.cos ((Fin.cons (0:ℝ) z : Fin (2*k+1) → ℝ) i-(Fin.cons (0:ℝ) z : Fin (2*k+1) → ℝ) j):ℂ) else 1).re := by
  rw [forest_regularProbability_integral]
  simp_rw [rootIntegral_closed,forest_signedKernel,empty_signedKernel]

end RegularFourier
