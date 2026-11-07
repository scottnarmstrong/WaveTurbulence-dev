/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchPieceData
/-! Actual transport of the layer, hinge set and counting fields of pieces.
This record deliberately does not assert the remaining Cs/gap compatibility. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist LGSpine
variable {d R : ℕ}

/-- The actual piece fields already proved invariant; gap and collection choices remain separate. -/
structure PieceFieldIso (π ρ : Stage1PieceD d R) where
  iso : MolIso π.Gsb.molecule ρ.Gsb.molecule
  layer : ∀ c, ρ.layer (iso.e c) = π.layer c
  hinges : iso.img π.Cs.hinges = ρ.Cs.hinges
  gsk : ρ.gsk = π.gsk
  bsk : ρ.bsk = π.bsk

namespace PieceFieldIso
variable {π ρ θ : Stage1PieceD d R}

noncomputable def refl (π : Stage1PieceD d R) : PieceFieldIso π π where
  iso := molIsoRefl π.Gsb
  layer _ := rfl
  hinges := Finset.image_id
  gsk := rfl
  bsk := rfl

noncomputable def symm (h : PieceFieldIso π ρ) : PieceFieldIso ρ π where
  iso := h.iso.symm
  layer c := by
    have he := (h.layer (h.iso.e.symm c)).symm
    simpa only [MolIso.symm, Equiv.apply_symm_apply] using he
  hinges := by
    have he := congrArg h.iso.symm.img h.hinges
    rw [h.iso.img_img_symm] at he
    exact he.symm
  gsk := h.gsk.symm
  bsk := h.bsk.symm

noncomputable def trans (h : PieceFieldIso π ρ) (k : PieceFieldIso ρ θ) : PieceFieldIso π θ where
  iso := molIsoTrans h.iso k.iso
  layer c := (k.layer (h.iso.e c)).trans (h.layer c)
  hinges := by
    rw [molIsoTrans_img, h.hinges, k.hinges]
  gsk := k.gsk.trans h.gsk
  bsk := k.bsk.trans h.bsk

end PieceFieldIso

/-- Actual selected batches transport the independently constructed basic piece fields. -/
noncomputable def BatchIso.pieceFieldIso {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction (2 * R) ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    PieceFieldIso (stage1PieceOf d A.plain A.layered A.decodes σ)
      (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)) where
  iso := h.spliceMolIso σ hA
  layer := h.piece_layer σ hA d
  hinges := h.piece_hinges σ hA d
  gsk := h.piece_gsk σ hA d
  bsk := h.piece_bsk σ hA d

end WaveTurbulence.VineA
