/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGreg
/-! The actual constructed Stage 1 piece has invariant gsk along selected batches. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open LFTwist RedSplice Stage1
variable {R p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction (2 * R) ι}
variable {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Full actual gsk invariance: regular rows and actual chosen vine indices are both transported. -/
theorem BatchIso.piece_gsk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (d : ℕ) :
    (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)).gsk =
      (stage1PieceOf d A.plain A.layered A.decodes σ).gsk := by
  change gskOf (RedSplice.gregOf B.data B.plain B.layered) B.skeleton (transportPrescription F σ)
      (RegRed.coreLayer B.layered B.data B.plain B.decodes) =
    gskOf (RedSplice.gregOf A.data A.plain A.layered) A.skeleton σ
      (RegRed.coreLayer A.layered A.data A.plain A.decodes)
  unfold gskOf
  rw [h.gregOf, h.vineIndexSum σ hA]

end WaveTurbulence.VineA
