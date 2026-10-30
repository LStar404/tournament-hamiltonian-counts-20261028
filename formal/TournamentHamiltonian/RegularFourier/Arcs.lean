module

public import TournamentHamiltonian.RegularFourier.Integral
public import TournamentHamiltonian.TorusCluster.Product
public import TournamentHamiltonian.ForestGaussian.Edges

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation UniformBlowup TorusCluster
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def imbalance {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) (i : Fin m) : ℤ :=
  ∑ e∈s, ((if i=winner ω e then (1:ℤ) else 0)-(if i=loser ω e then (1:ℤ) else 0))

lemma imbalance_counts {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) (i : Fin m) :
    imbalance s ω i = ((s.filter (fun e => winner ω e=i)).card : ℤ)-
      ((s.filter (fun e => loser ω e=i)).card : ℤ) := by
  simp only [imbalance,Finset.sum_sub_distrib]
  simp [eq_comm,Finset.sum_boole]

lemma sum_imbalance {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) :
    ∑ i,imbalance s ω i=0 := by
  unfold imbalance
  rw [Finset.sum_comm]
  simp [Finset.sum_sub_distrib]

lemma imbalance_angle {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) (x : Fin m → ℝ) :
    (∑ i,(imbalance s ω i : ℝ)*x i) = ∑ e∈s, (x (winner ω e)-x (loser ω e)) := by
  unfold imbalance
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [sub_mul,ite_mul,one_mul,zero_mul,Finset.sum_sub_distrib]
  simp

/-- Genuine exp (+i b·x): the plus sign follows from winner monomials X_winner
in constrainedPolynomial. There is no division by any cosine. -/
theorem signedKernel_phase {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) (x : Fin m → ℝ) :
    signedKernel s ω x = cis (∑ i,(imbalance s ω i : ℝ)*x i) *
      ∏ e∈sᶜ,(Real.cos (x e.val.1-x e.val.2):ℂ) := by
  rw [imbalance_angle,cis_sum]
  unfold signedKernel signedFactor
  rw [Finset.prod_ite]
  have hs : Finset.univ.filter (fun e : Edge m => e∈s)=s := by ext; simp
  have hc : Finset.univ.filter (fun e : Edge m => e∉s)=sᶜ := by ext; simp
  rw [hs,hc]

def edgeSym {m : ℕ} (e : Edge m) : Sym2 (Fin m) := s(e.val.1,e.val.2)
lemma edgeSym_injective {m : ℕ} : Function.Injective (edgeSym (m:=m)) := by
  intro e f h
  rcases Sym2.eq_iff.mp h with h|h
  · apply Subtype.ext
    exact Prod.ext h.1 h.2
  · have he := e.property
    have hf := f.property
    rw [h.1,h.2] at he
    exact False.elim (lt_asymm he hf)

def selectedGraph {m : ℕ} (s : Finset (Edge m)) : SimpleGraph (Fin m) :=
  SimpleGraph.fromEdgeSet (↑(s.image edgeSym))

lemma selectedGraph_edge {m : ℕ} (s : Finset (Edge m)) (e : Edge m) :
    (selectedGraph s).Adj e.val.1 e.val.2 ↔ e∈s := by
  rw [selectedGraph,SimpleGraph.fromEdgeSet_adj]
  simp only [Finset.mem_coe,Finset.mem_image]
  constructor
  · rintro ⟨⟨f,hf,he⟩,_⟩
    have hfe := edgeSym_injective he
    simpa only [hfe] using hf
  · intro he
    exact ⟨⟨e,he,rfl⟩,ne_of_lt e.property⟩

lemma edgeSym_exists {m : ℕ} (i j : Fin m) (h : i≠j) :
    ∃ e : Edge m, edgeSym e=s(i,j) := by
  rcases lt_or_gt_of_ne h with h|h
  · exact ⟨⟨(i,j),h⟩,rfl⟩
  · exact ⟨⟨(j,i),h⟩,Sym2.eq_swap⟩

lemma complement_edgeFinset {m : ℕ} (s : Finset (Edge m)) :
    (selectedGraph s)ᶜ.edgeFinset=sᶜ.image edgeSym := by
  ext e
  induction e using Sym2.ind with
  | _ i j =>
      by_cases hij : i=j
      · subst j
        simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,SimpleGraph.irrefl,
          Finset.mem_image,false_iff,not_exists,not_and]
        intro e _ he
        rcases Sym2.eq_iff.mp he with h|h <;>
          have hh := e.property <;> rw [h.1,h.2] at hh <;> exact (lt_irrefl _ hh)
      · obtain ⟨e,he⟩ := edgeSym_exists i j hij
        rw [← he]
        rw [SimpleGraph.mem_edgeFinset]
        change (selectedGraph s)ᶜ.Adj e.val.1 e.val.2 ↔ _
        rw [SimpleGraph.compl_adj,selectedGraph_edge]
        rw [Finset.mem_image]
        constructor
        · intro h
          exact ⟨e,by simpa using h.2,rfl⟩
        · rintro ⟨f,hf,hfe⟩
          have h := edgeSym_injective hfe
          exact ⟨ne_of_lt e.property, by simpa only [h,Finset.mem_compl] using hf⟩

/-- The norm is exactly the previously certified absolute cosine product on K_m−H. -/
theorem signedKernel_norm {m : ℕ} (s : Finset (Edge m)) (ω : Orientation m) (x : Fin m → ℝ) :
    ‖signedKernel s ω x‖ = TorusCluster.kernel (selectedGraph s) x := by
  rw [signedKernel_phase,norm_mul,cis_norm,one_mul,norm_prod]
  unfold TorusCluster.kernel
  rw [complement_edgeFinset,Finset.prod_image (fun _ _ _ _ h => edgeSym_injective h)]
  apply Finset.prod_congr rfl
  intro e _
  simp only [Complex.norm_real,Real.norm_eq_abs,edgeSym,TorusCluster.edgeFactor_mk]

end RegularFourier
