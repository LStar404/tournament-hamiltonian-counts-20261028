module

public import TournamentHamiltonian.TorusCluster.Endpoint
public import TournamentHamiltonian.TorusCluster.CosineGaussian
public import Mathlib.Algebra.BigOperators.Sym

@[expose] public section

set_option autoImplicit false
namespace TorusCluster
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

/-- Squared difference attached to an actual unordered edge. -/
def sqFactor (z : Fin m → ℝ) : Sym2 (Fin m) → ℝ :=
  Sym2.lift ⟨fun i j => (z i-z j)^2, fun i j => by dsimp; ring⟩
@[simp] lemma sqFactor_mk (z : Fin m → ℝ) (i j : Fin m) :
    sqFactor z s(i,j) = (z i-z j)^2 := rfl

def graphEnergy (G : SimpleGraph (Fin m)) (z : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  ∑ e ∈ S.sym2, if e ∈ G.edgeFinset then sqFactor z e else 0

def completeEnergy (z : Fin m → ℝ) (S : Finset (Fin m)) : ℝ := ∑ e ∈ S.sym2, sqFactor z e

def meanOn (z : Fin m → ℝ) (S : Finset (Fin m)) : ℝ := (∑ i ∈ S, z i)/(S.card : ℝ)
def varianceOn (z : Fin m → ℝ) (S : Finset (Fin m)) : ℝ := ∑ i ∈ S, (z i-meanOn z S)^2

/-- Finite unordered-pair/double-sum conversion. Diagonal factors are zero. -/
lemma twice_sum_sym2 (S : Finset (Fin m)) (f : Sym2 (Fin m) → ℝ)
    (hdiag : ∀ i, f s(i,i) = 0) :
    2*(∑ e ∈ S.sym2, f e) = ∑ i ∈ S, ∑ j ∈ S, f s(i,j) := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih =>
    simp only [Finset.sym2_cons, Finset.sum_disjUnion, Finset.sum_map,
      Finset.sum_cons, Sym2.mkEmbedding_apply, hdiag, zero_add]
    rw [Finset.sum_add_distrib]
    have hs : (∑ i ∈ S, f s(i,a)) = ∑ i ∈ S, f s(a,i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Sym2.eq_swap]
    rw [hs]
    linarith

lemma twice_graphEnergy (G : SimpleGraph (Fin m)) (z : Fin m → ℝ) (S : Finset (Fin m)) :
    2*graphEnergy G z S = ∑ i ∈ S, ∑ j ∈ S, if G.Adj i j then (z i-z j)^2 else 0 := by
  have hh := twice_sum_sym2 S (fun e => if e ∈ G.edgeFinset then sqFactor z e else 0)
    (by intro i; simp)
  simpa only [graphEnergy, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    sqFactor_mk] using hh

lemma twice_completeEnergy (z : Fin m → ℝ) (S : Finset (Fin m)) :
    2*completeEnergy z S = ∑ i ∈ S, ∑ j ∈ S, (z i-z j)^2 := by
  exact twice_sum_sym2 S (sqFactor z) (by intro i; simp)

lemma graphEnergy_compl_add (H : SimpleGraph (Fin m)) (z : Fin m → ℝ) (S : Finset (Fin m)) :
    graphEnergy Hᶜ z S + graphEnergy H z S = completeEnergy z S := by
  unfold graphEnergy completeEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.ind with
  | _ i j =>
    by_cases hij : i = j
    · subst j; simp
    · by_cases ha : H.Adj i j <;> simp [SimpleGraph.compl_adj, hij, ha]

lemma graphEnergy_translate (G : SimpleGraph (Fin m)) (z : Fin m → ℝ)
    (S : Finset (Fin m)) (c : ℝ) : graphEnergy G (fun i => z i-c) S = graphEnergy G z S := by
  unfold graphEnergy
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.ind with
  | _ i j => simp only [sqFactor_mk, sub_sub_sub_cancel_right]

lemma completeEnergy_translate (z : Fin m → ℝ) (S : Finset (Fin m)) (c : ℝ) :
    completeEnergy (fun i => z i-c) S = completeEnergy z S := by
  unfold completeEnergy
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.ind with
  | _ i j => simp only [sqFactor_mk, sub_sub_sub_cancel_right]

lemma sum_centered_eq_zero (z : Fin m → ℝ) (S : Finset (Fin m)) :
    (∑ i ∈ S, (z i-meanOn z S)) = 0 := by
  by_cases hS : S.card = 0
  · have he := Finset.card_eq_zero.mp hS
    subst S; simp
  · have hp : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, meanOn]
    field_simp
    ring

lemma double_sq_sum (z : Fin m → ℝ) (S : Finset (Fin m)) :
    (∑ i ∈ S, ∑ j ∈ S, (z i-z j)^2) =
      2*(S.card : ℝ)*(∑ i ∈ S, z i^2)-2*(∑ i ∈ S, z i)^2 := by
  simp_rw [show ∀ i j, (z i-z j)^2 = z i^2+z j^2-2*z i*z j by intros; ring]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma completeEnergy_eq_variance (z : Fin m → ℝ) (S : Finset (Fin m)) :
    completeEnergy z S = (S.card : ℝ)*varianceOn z S := by
  have he := twice_completeEnergy (fun i => z i-meanOn z S) S
  rw [completeEnergy_translate, double_sq_sum, sum_centered_eq_zero] at he
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at he
  unfold varianceOn
  linarith

lemma deleted_neighbors_le_two (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (S : Finset (Fin m)) (i : Fin m) : (S.filter (H.Adj i)).card ≤ 2 := by
  apply le_trans _ (hdegree i)
  rw [← H.card_neighborFinset_eq_degree, H.neighborFinset_eq_filter]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

lemma adjacency_sq_left_le (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (z : Fin m → ℝ) (S : Finset (Fin m)) :
    (∑ i ∈ S, ∑ j ∈ S, if H.Adj i j then z i^2 else 0) ≤ 2*∑ i ∈ S, z i^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    (∑ j ∈ S, if H.Adj i j then z i^2 else 0) = ∑ j ∈ S.filter (H.Adj i), z i^2 := by
      rw [Finset.sum_filter]
    _ = ((S.filter (H.Adj i)).card : ℝ)*z i^2 := by simp
    _ ≤ 2*z i^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast deleted_neighbors_le_two H hdegree S i) (sq_nonneg _)

lemma adjacency_sq_right_le (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (z : Fin m → ℝ) (S : Finset (Fin m)) :
    (∑ i ∈ S, ∑ j ∈ S, if H.Adj i j then z j^2 else 0) ≤ 2*∑ i ∈ S, z i^2 := by
  rw [Finset.sum_comm]
  simp_rw [H.adj_comm]
  exact adjacency_sq_left_le H hdegree z S

/-- Missing-degree two gives precisely the loss 4, for any induced vertex set. -/
lemma deleted_energy_le_four (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (z : Fin m → ℝ) (S : Finset (Fin m)) :
    graphEnergy H z S ≤ 4*∑ i ∈ S, z i^2 := by
  have hh : (∑ i ∈ S, ∑ j ∈ S, if H.Adj i j then (z i-z j)^2 else 0) ≤
      2*(∑ i ∈ S, ∑ j ∈ S, if H.Adj i j then z i^2 else 0) +
      2*(∑ i ∈ S, ∑ j ∈ S, if H.Adj i j then z j^2 else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases ha : H.Adj i j <;> simp only [ha, ite_true, ite_false] <;>
      nlinarith [sq_nonneg (z i+z j)]
  rw [← twice_graphEnergy] at hh
  have h1 := adjacency_sq_left_le H hdegree z S
  have h2 := adjacency_sq_right_le H hdegree z S
  linarith

/-- Actual retained quadratic energy ≥ (p−4) times centered variance. -/
theorem retained_energy_lower (H : SimpleGraph (Fin m)) (hdegree : ∀ i, H.degree i ≤ 2)
    (z : Fin m → ℝ) (S : Finset (Fin m)) :
    ((S.card : ℝ)-4)*varianceOn z S ≤ graphEnergy Hᶜ z S := by
  have hdel := deleted_energy_le_four H hdegree (fun i => z i-meanOn z S) S
  rw [graphEnergy_translate] at hdel
  have hsplit := graphEnergy_compl_add H z S
  rw [completeEnergy_eq_variance] at hsplit
  change graphEnergy H z S ≤ 4*varianceOn z S at hdel
  nlinarith

end
end TorusCluster
