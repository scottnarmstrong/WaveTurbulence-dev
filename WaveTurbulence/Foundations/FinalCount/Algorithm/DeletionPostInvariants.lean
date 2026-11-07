/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ConditionedDeletionInvariants
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # Complete inherited invariants of any literal conditioned deletion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

structure DeletionPostInvariants {M : Molecule V D} {B : AppbPattern}
    (r : AppbRealization M B) {d : ℕ} (L g : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (q : Fin B.edges.length → (Fin d → ℤ)) : Prop where
  molecule : r.post.IsMolecule
  noLoops : AppbNoLoops r.post
  noTripleBonds : AppbNoTripleBonds r.post
  largeGap : ∀ ζ,r.conditionedPostAdmissibility A q ζ → AppbLargeGap r.post L w ζ g
  mateLabels : ∀ ζ,r.conditionedPostAdmissibility A q ζ → ∀ x,ζ (r.post.mate x) = ζ x
  validLinkScales : ∀ c,AppbValidLinkScales M L w A c P →
    AppbValidLinkScales r.post L w (r.conditionedPostAdmissibility A q) c P

theorem deletionPostInvariants {M : Molecule V D} {B : AppbPattern}
    (r : AppbRealization M B) {d : ℕ} (L g : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (q : Fin B.edges.length → (Fin d → ℤ)) (hM : M.IsMolecule)
    (hno : AppbNoLoops M) (hnt : AppbNoTripleBonds M)
    (hLG : ∀ κ,A κ → AppbLargeGap M L w κ g) : DeletionPostInvariants r L g w A P q where
  molecule := appb_eraseAtoms_isMolecule M hM r.removedAtoms
  noLoops := appb_eraseAtoms_noLoops M r.removedAtoms hno
  noTripleBonds := appb_eraseAtoms_noTripleBonds M r.removedAtoms hnt
  largeGap := conditionedPost_largeGap r q hLG
  mateLabels := conditionedPost_mate_labels r A q
  validLinkScales := fun _ hv => r.conditionedPost_validLinkScales hv q

end WaveTurbulence.Mole.AppbAlgorithm
