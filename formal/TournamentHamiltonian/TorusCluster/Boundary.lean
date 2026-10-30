module

public import TournamentHamiltonian.TorusCluster.LocalProduct

@[expose] public section

set_option autoImplicit false
namespace TorusCluster
noncomputable section
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma circleDist_self (a : ℝ) : circleDist a a = 0 := by simp [circleDist]

/-- Multi-period representatives have precisely zero distance. -/
example (a : ℝ) (k : ℤ) : circleDist (a-k*Real.pi) a = 0 := by
  rw [circleDist_sub_int_pi, circleDist_self]

/-- The endpoint of the local interval causes no division-by-zero gap. -/
example : |Real.cos (Real.pi/2)| ≤ Real.exp (-((Real.pi/2)^2/2)) := by
  apply abs_cos_le_gaussian
  rw [abs_of_pos (by positivity : 0 < Real.pi/2)]

/-- The lower allowed order is covered for the actual real angle configuration. -/
example (x : Fin 64 → ℝ) :
    ∃ j : Fin 16, (64:ℝ)/16 ≤ (core x (center j)).card := exists_large_core x

lemma constant_kernel {m : ℕ} (H : SimpleGraph (Fin m)) (a : ℝ) :
    kernel H (fun _ => a) = 1 := by
  apply Finset.prod_eq_one
  intro e _
  induction e using Sym2.ind with
  | _ i j => simp

/-- Empty local sets use the same variance and energy definitions. -/
example {m : ℕ} (H : SimpleGraph (Fin m)) (z : Fin m → ℝ) :
    insideProduct H z ∅ = 1 ∧ varianceOn z ∅ = 0 ∧ graphEnergy Hᶜ z ∅ = 0 := by
  constructor
  · unfold insideProduct insideEdges
    have he : Hᶜ.edgeFinset.filter (fun e => e.toFinset ⊆ ∅) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have hs := (Finset.mem_filter.mp he).2
      induction e using Sym2.ind with
      | _ i j => exact Finset.notMem_empty i (hs (by simp))
    rw [he, Finset.prod_empty]
  · simp [varianceOn, graphEnergy]

end
end TorusCluster
