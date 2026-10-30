module

public import TournamentHamiltonian.RegularFourier.Arcs

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace RegularFourier
open MeasureTheory Set Function PeriodicBox MvPolynomial RegularOrientation UniformBlowup
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def forestEdges {m : ℕ} (F : ForestGaussian.EdgeSet m) : Finset (Edge m) :=
  Finset.univ.filter (fun e => (ForestGaussian.graph F).Adj e.val.1 e.val.2)
def forestOrientation {m : ℕ} (F : ForestGaussian.EdgeSet m) : Orientation m :=
  fun e => decide ((e.val.1,e.val.2)∈F.edges)
def arc {m : ℕ} (ω : Orientation m) (e : Edge m) : Fin m × Fin m :=
  (winner ω e,loser ω e)
lemma arc_injective {m : ℕ} (ω : Orientation m) : Function.Injective (arc ω) := by
  intro e f h
  apply edgeSym_injective
  have hs (e : Edge m) : edgeSym e=s((arc ω e).1,(arc ω e).2) := by
    cases he : ω e <;> simp [arc,winner,loser,edgeSym,he,Sym2.eq_swap]
  rw [hs e,hs f,h]

lemma forest_arc_mem {m : ℕ} (F : ForestGaussian.EdgeSet m) (e : Edge m)
    (he : e∈forestEdges F) : arc (forestOrientation F) e∈F.edges := by
  have hg : (e.val.1,e.val.2)∈F.edges ∨ (e.val.2,e.val.1)∈F.edges := by
    simpa only [forestEdges,Finset.mem_filter,Finset.mem_univ,true_and,ForestGaussian.graph] using he
  by_cases h : (e.val.1,e.val.2)∈F.edges
  · simp [arc,winner,loser,forestOrientation,h]
  · simpa [arc,winner,loser,forestOrientation,h] using hg.resolve_left h

lemma forest_arc_surj {m : ℕ} (F : ForestGaussian.EdgeSet m) (p : Fin m × Fin m)
    (hp : p∈F.edges) : ∃ e∈forestEdges F, arc (forestOrientation F) e=p := by
  have hne : p.1≠p.2 := by
    intro h
    apply F.loopless p.2
    have hp' : (p.1,p.2)∈F.edges := hp
    rw [h] at hp'
    exact hp'
  rcases lt_or_gt_of_ne hne with h|h
  · let e : Edge m := ⟨p,h⟩
    refine ⟨e,?_,?_⟩
    · simp only [forestEdges,Finset.mem_filter,Finset.mem_univ,true_and,ForestGaussian.graph]
      exact Or.inl hp
    · simp only [arc,winner,loser,forestOrientation,e,hp,decide_true,ite_true,Prod.eta]
  · let e : Edge m := ⟨(p.2,p.1),h⟩
    have hr := F.no_reverse p.1 p.2 hp
    refine ⟨e,?_,?_⟩
    · simp only [forestEdges,Finset.mem_filter,Finset.mem_univ,true_and,ForestGaussian.graph,e]
      exact Or.inr hp
    · simp only [arc,winner,loser,forestOrientation,e,hr,decide_false,Bool.false_eq_true,
        ite_false,Prod.eta]

/-- The canonical prescribed pairs and their winner directions recover the actual arcs exactly. -/
theorem forest_arc_image {m : ℕ} (F : ForestGaussian.EdgeSet m) :
    (forestEdges F).image (arc (forestOrientation F))=F.edges := by
  ext p
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e,he,rfl⟩
    exact forest_arc_mem F e he
  · exact forest_arc_surj F p

theorem forest_edge_count {m : ℕ} (F : ForestGaussian.EdgeSet m) :
    (forestEdges F).card=ForestGaussian.edgeCount F := by
  rw [ForestGaussian.edgeCount,← forest_arc_image,Finset.card_image_of_injective _ (arc_injective _)]

theorem forest_graph {m : ℕ} (F : ForestGaussian.EdgeSet m) :
    selectedGraph (forestEdges F)=ForestGaussian.graph F := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [SimpleGraph.irrefl]
  · rcases lt_or_gt_of_ne hij with h|h
    · have he := selectedGraph_edge (forestEdges F) (⟨(i,j),h⟩ : Edge m)
      simpa only [forestEdges,Finset.mem_filter,Finset.mem_univ,true_and] using he
    · rw [(selectedGraph (forestEdges F)).adj_comm, (ForestGaussian.graph F).adj_comm]
      have he := selectedGraph_edge (forestEdges F) (⟨(j,i),h⟩ : Edge m)
      simpa only [forestEdges,Finset.mem_filter,Finset.mem_univ,true_and] using he

lemma directed_sum {m : ℕ} (E : Finset (Fin m × Fin m)) (i : Fin m) :
    (∑ p∈E, ((if i=p.1 then (1:ℝ) else 0)-(if i=p.2 then (1:ℝ) else 0))) =
      (ForestGaussian.outCount E i : ℝ)-ForestGaussian.inCount E i := by
  have he : (∑ p∈E, ((if i=p.1 then (1:ℝ) else 0)-(if i=p.2 then (1:ℝ) else 0))) =
      ∑ p : Fin m × Fin m, if p∈E then
        ((if i=p.1 then (1:ℝ) else 0)-(if i=p.2 then (1:ℝ) else 0)) else 0 := by simp
  rw [he,Fintype.sum_prod_type]
  have hp (j l : Fin m) : (if (j,l)∈E then
      ((if i=j then (1:ℝ) else 0)-(if i=l then (1:ℝ) else 0)) else 0) =
      (if i=j then (if (j,l)∈E then (1:ℝ) else 0) else 0)-
      (if i=l then (if (j,l)∈E then (1:ℝ) else 0) else 0) := by split_ifs <;> ring
  simp_rw [hp,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f:=fun j l => if i=l then (if (j,l)∈E then (1:ℝ) else 0) else 0)]
  simp [ForestGaussian.outCount,ForestGaussian.inCount,Finset.sum_ite_irrel]

/-- The real endpoint imbalance in frozen Gaussian APIs equals the integer Fourier imbalance. -/
theorem forest_imbalance {m : ℕ} (F : ForestGaussian.EdgeSet m) (i : Fin m) :
    (imbalance (forestEdges F) (forestOrientation F) i : ℝ)=ForestGaussian.imbalance F i := by
  rw [ForestGaussian.imbalance,← directed_sum]
  rw [← forest_arc_image,Finset.sum_image (fun _ _ _ _ h => arc_injective _ h)]
  unfold imbalance arc
  push_cast
  rfl

/-- Actual regular containment of F, not an abstract coefficient predicate. -/
theorem forest_contains {m : ℕ} (F : ForestGaussian.EdgeSet m) (T : TournamentHamiltonian.Tournament m) :
    Contains T (forestEdges F) (forestOrientation F) ↔ ∀ p∈F.edges,T.val p.1 p.2=true := by
  rw [← forest_arc_image]
  simp only [Contains,Finset.forall_mem_image,arc]

lemma forest_kernel_norm {m : ℕ} (F : ForestGaussian.EdgeSet m) (x : Fin m → ℝ) :
    ‖signedKernel (forestEdges F) (forestOrientation F) x‖=TorusCluster.kernel (ForestGaussian.graph F) x := by
  rw [signedKernel_norm,forest_graph]

end RegularFourier
