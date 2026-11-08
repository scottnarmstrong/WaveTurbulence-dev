/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchSplice
/-! Actual layer, hinge and counting fields of Stage 1 pieces along selected batches. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist
variable {R p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction (2 * R) ι}
variable {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- B1b-2 (Mk-general form of `BatchIso.piece_layer`). -/
theorem BatchIso.piece_layerMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (d : ℕ)
    (c : GBranch (stSt A.skeleton σ Mk).G.tree) :
    (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ) Mk').layer
        ((h.spliceMolIsoMk σ hT hA).e c) =
      (stage1PieceOf d A.plain A.layered A.decodes σ Mk).layer c :=
  (congrArg (RegRed.coreLayer B.layered B.data B.plain B.decodes)
    (h.spliceMolIso_branch_namesMk σ hT hA c)).trans (h.coreLayer ((stSt A.skeleton σ Mk).M.ob c))

/-- Actual piece layers commute with the actual full batch quotient map. -/
theorem BatchIso.piece_layer (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (d : ℕ) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)).layer
        ((h.spliceMolIso σ hA).e c) =
      (stage1PieceOf d A.plain A.layered A.decodes σ).layer c :=
  h.piece_layerMk σ (Stage1Mk.markTransported_empty F) hA d c

/-- B1b-3 (Mk-general form of `BatchIso.piece_hinge_iff`). -/
theorem BatchIso.piece_hinge_iffMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (d : ℕ)
    (c : GBranch (stSt A.skeleton σ Mk).G.tree) :
    (h.spliceMolIsoMk σ hT hA).e c ∈
        (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ) Mk').Cs.hinges ↔
      c ∈ (stage1PieceOf d A.plain A.layered A.decodes σ Mk).Cs.hinges := h.splice_hinge_iffMk σ hT hA c

/-- The actual constructed hinge membership follows the actual batch map. -/
theorem BatchIso.piece_hinge_iff (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (d : ℕ) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (h.spliceMolIso σ hA).e c ∈
        (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)).Cs.hinges ↔
      c ∈ (stage1PieceOf d A.plain A.layered A.decodes σ).Cs.hinges :=
  h.piece_hinge_iffMk σ (Stage1Mk.markTransported_empty F) hA d c

/-- B1b-3 (Mk-general form of `BatchIso.piece_hinges`). -/
theorem BatchIso.piece_hingesMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (d : ℕ) :
    (stage1PieceOf d A.plain A.layered A.decodes σ Mk).Cs.hinges.image (h.spliceMolIsoMk σ hT hA).e =
      (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ) Mk').Cs.hinges :=
  h.splice_hinges_imageMk σ hT hA

/-- The actual full hinge sets of the constructed pieces correspond. -/
theorem BatchIso.piece_hinges (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (d : ℕ) :
    (stage1PieceOf d A.plain A.layered A.decodes σ).Cs.hinges.image (h.spliceMolIso σ hA).e =
      (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)).Cs.hinges :=
  h.piece_hingesMk σ (Stage1Mk.markTransported_empty F) hA d

/-- B1b-2 (Mk-general form of `BatchIso.piece_bsk`). -/
theorem BatchIso.piece_bskMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (d : ℕ) :
    (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ) Mk').bsk =
      (stage1PieceOf d A.plain A.layered A.decodes σ Mk).bsk := h.badCountMk σ Mk Mk' hA hT

/-- The actual constructed bsk follows every selected batch. -/
theorem BatchIso.piece_bsk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (d : ℕ) :
    (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)).bsk =
      (stage1PieceOf d A.plain A.layered A.decodes σ).bsk :=
  h.piece_bskMk σ (Stage1Mk.markTransported_empty F) hA d

end WaveTurbulence.VineA
