/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBValidLinkScales
public import WaveTurbulence.Foundations.FinalCount.AppBLargeGap
import Mathlib.Tactic

/-! # The concrete conditioned post predicates retain physical input tests -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem conditionedPost_largeGap {d : ℕ} {L g : ℝ} {w : Mom d}
    {A : (D → (Fin d → ℤ)) → Prop} (q : Fin P.edges.length → (Fin d → ℤ))
    (h : ∀ κ,A κ → AppbLargeGap M L w κ g) :
    ∀ ζ,r.conditionedPostAdmissibility A q ζ → AppbLargeGap r.post L w ζ g := by
  rintro ζ ⟨κ,hκ,hm,hq,hr⟩
  rw [← hr]
  exact appb_largeGap_eraseAtoms M r.removedAtoms (h κ hκ)

theorem conditionedPost_mate_labels {d : ℕ}
    (A : (D → (Fin d → ℤ)) → Prop) (q : Fin P.edges.length → (Fin d → ℤ)) :
    ∀ ζ,r.conditionedPostAdmissibility A q ζ → ∀ x,ζ (r.post.mate x) = ζ x := by
  rintro ζ ⟨κ,hκ,hm,hq,hr⟩ x
  rw [← hr]
  exact hm x.val

end WaveTurbulence.Mole.AppbAlgorithm
