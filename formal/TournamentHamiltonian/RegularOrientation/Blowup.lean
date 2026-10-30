module

public import TournamentHamiltonian.RegularOrientation.Boundary

@[expose] public section

set_option autoImplicit false

namespace RegularOrientation
open TournamentHamiltonian UniformBlowup
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Genuine independent uniformly chosen regular labelled internal blocks. -/
abbrev RegularSample (d k : ℕ) := Fin d → RegularTournament (2*k+1)

def regularSampleWitness (d k : ℕ) : RegularSample d k := fun _ => regularCarousel k

theorem regularSample_card (d k : ℕ) :
    Fintype.card (RegularSample d k) =
      ((orientationPolynomial (2*k+1)).coeff (regularExponent k))^d := by
  rw [Fintype.card_fun, Fintype.card_fin, regular_card_eq_coeff]

theorem regularSample_card_pos (d k : ℕ) : 0 < Fintype.card (RegularSample d k) :=
  Fintype.card_pos_iff.mpr ⟨regularSampleWitness d k⟩

def regularSampleBits {d k : ℕ} (ω : RegularSample d k) : Sample d (2*k+1) :=
  (blockTournamentEquiv d (2*k+1)).symm (fun i => (ω i).val)

/-- The regular model is an actual blowup tournament using these same internal
blocks and deterministic cross-block directions from the base. -/
def regularBlowup {d k : ℕ} (T : Tournament d) (ω : RegularSample d k)
    (e : Fin (d*(2*k+1)) ≃ Vertex d (2*k+1)) : Tournament (d*(2*k+1)) :=
  blowup T (regularSampleBits ω) e

theorem regular_internal_arc {d k : ℕ} (T : Tournament d) (ω : RegularSample d k)
    (i : Fin d) (a b : Fin (2*k+1)) :
    arc T (regularSampleBits ω) (i,a) (i,b) = (ω i).val.val a b := by
  rw [arc_same_block]
  simp only [regularSampleBits, Equiv.apply_symm_apply]

end
end RegularOrientation
