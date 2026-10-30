module

public import TournamentHamiltonian.UniformBlowup.Cycle
public import TournamentHamiltonian.RegularOrientation.Blowup

@[expose] public section

set_option autoImplicit false
namespace BaseRelabel
open TournamentHamiltonian UniformBlowup RegularOrientation
noncomputable section

/-- Actual block-vertex relabelling, leaving internal labels fixed. -/
def vertexEquiv {d m : ℕ} (e : Equiv.Perm (Fin d)) : Equiv.Perm (Vertex d m) :=
  Equiv.prodCongr e (Equiv.refl _)

/-- Reindex the independent Boolean block samples by the inverse base permutation. -/
def sampleEquiv {d m : ℕ} (e : Equiv.Perm (Fin d)) : Equiv.Perm (Sample d m) where
  toFun ω c := ω (e.symm c.1, c.2)
  invFun ω c := ω (e c.1, c.2)
  left_inv ω := by funext c; simp
  right_inv ω := by funext c; simp

@[simp] theorem vertexEquiv_apply {d m : ℕ} (e : Equiv.Perm (Fin d))
    (u : Vertex d m) : vertexEquiv e u = (e u.1, u.2) := rfl

@[simp] theorem sampleEquiv_apply {d m : ℕ} (e : Equiv.Perm (Fin d))
    (ω : Sample d m) (c : Coord d m) : sampleEquiv e ω c = ω (e.symm c.1,c.2) := rfl

/-- Equality of the actual arcs, not of a weight matrix or spectral proxy. -/
theorem arc_relabel {d m : ℕ} (T : Tournament d) (e : Equiv.Perm (Fin d))
    (ω : Sample d m) (u v : Vertex d m) :
    arc (relabelTournament T e) ω u v =
      arc T (sampleEquiv e ω) (vertexEquiv e u) (vertexEquiv e v) := by
  simp [arc, relabelTournament, e.injective.eq_iff]

/-- Reindex whole regular blocks, without treating their internal edges as independent. -/
def regularSampleEquiv {d k : ℕ} (e : Equiv.Perm (Fin d)) :
    Equiv.Perm (RegularSample d k) where
  toFun ω i := ω (e.symm i)
  invFun ω i := ω (e i)
  left_inv ω := by funext i; simp
  right_inv ω := by funext i; simp

@[simp] theorem regularSampleEquiv_apply {d k : ℕ} (e : Equiv.Perm (Fin d))
    (ω : RegularSample d k) (i : Fin d) : regularSampleEquiv e ω i = ω (e.symm i) := rfl

/-- The two sample permutations commute with the actual bits encoding. -/
theorem regularSampleBits_equiv {d k : ℕ} (e : Equiv.Perm (Fin d))
    (ω : RegularSample d k) :
    regularSampleBits (regularSampleEquiv e ω) = sampleEquiv e (regularSampleBits ω) := by
  funext c
  rfl

end
end BaseRelabel
