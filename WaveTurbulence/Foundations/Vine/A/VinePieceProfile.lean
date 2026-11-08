/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGapProfile
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.Vine.A.VinePieceFieldIso
/-! Complete kernel-relevant A4 data with the actual successor gap product. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist LGSpine
variable {w R p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}

/-- A4 data retain the whole gap functional, with the exact garden, layer, hinges and counts. -/
structure PieceProfile (w : ℕ) where
  gap : GapProfile w
  layer : GBranch gap.garden.tree → ℕ
  hinges : Finset (GBranch gap.garden.tree)
  gsk : ℕ
  bsk : ℕ

/-- Equality uses the unique cast arising from literal equality of the normalized garden. -/
theorem PieceProfile.eq_of_fields {P Q : PieceProfile w} (hg : Q.gap = P.gap)
    (hl : ∀ b, Q.layer b = P.layer (gardenBranchCast (congrArg GapProfile.garden hg) b))
    (hh : Q.hinges.image (gardenBranchCast (congrArg GapProfile.garden hg)) = P.hinges)
    (hgs : Q.gsk = P.gsk) (hbs : Q.bsk = P.bsk) : Q = P := by
  rcases P with ⟨g, l, hs, k, b⟩
  rcases Q with ⟨g', l', hs', k', b'⟩
  change g' = g at hg
  subst g'
  have he : l' = l := funext hl
  have hh' : hs' = hs := by
    change hs'.image id = hs at hh
    simpa only [Finset.image_id] using hh
  change k' = k at hgs
  change b' = b at hbs
  subst l' hs' k' b'
  rfl

/-- B1b-3 (Mk-general form of `familyPieceProfile`): the piece fields at the marking `Mk`. -/
noncomputable def familyPieceProfileMk (A : FamilyReconstruction (2 * R) ι) (σ : Prescription A.skeleton)
    (Mk : Set (CLVine A.skeleton)) : PieceProfile (2 * R) where
  gap := gapProfileMk A.skeleton σ Mk
  layer := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ Mk).layer
  hinges := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ Mk).Cs.hinges
  gsk := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ Mk).gsk
  bsk := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ Mk).bsk

/-- B1b-3 (Mk-general form of `BatchIso.pieceProfile`): A4 field constancy at markings carried by the batch, given
B2c's dart-label gap identity (`GapValueSelDartsMk`). -/
theorem BatchIso.pieceProfileMk {A B : FamilyReconstruction (2 * R) ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (hg : GapValueSelDartsMk (2 * R)) :
    familyPieceProfileMk B (transportPrescription F σ) Mk' = familyPieceProfileMk A σ Mk := by
  apply PieceProfile.eq_of_fields (h.gapProfileMk σ hT hA hg)
  · intro b
    obtain ⟨a, rfl⟩ := (h.spliceMolIsoMk σ hT hA).e.surjective b
    change (stage1PieceOf 0 B.plain B.layered B.decodes (transportPrescription F σ) Mk').layer _ = _
    rw [h.piece_layerMk σ hT hA 0]
    exact congrArg (fun a => (stage1PieceOf 0 A.plain A.layered A.decodes σ Mk).layer a)
      (h.splice_branch_castMk σ hT hA a).symm
  · have hh := h.splice_hinges_imageMk σ hT hA
    change ((stSt B.skeleton (transportPrescription F σ) Mk').hinges).image
      (gardenBranchCast (h.splice_garden_eqMk σ hT hA)) = (stSt A.skeleton σ Mk).hinges
    rw [← hh, Finset.image_image]
    have he : (fun a => gardenBranchCast (h.splice_garden_eqMk σ hT hA)
        ((h.spliceMolIsoMk σ hT hA).e a)) = id := funext (h.splice_branch_castMk σ hT hA)
    exact (congrArg (fun f => (stSt A.skeleton σ Mk).hinges.image f) he).trans Finset.image_id
  · exact h.piece_gskMk σ hT hA 0
  · exact h.piece_bskMk σ hT hA 0

/-- Extract exactly the independently constructed successor piece fields. -/
noncomputable def familyPieceProfile (A : FamilyReconstruction (2 * R) ι) (σ : Prescription A.skeleton) :
    PieceProfile (2 * R) where
  gap := gapProfile A.skeleton σ
  layer := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ).layer
  hinges := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ).Cs.hinges
  gsk := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ).gsk
  bsk := (NormalizedSplice.stage1PieceOf 0 A.plain A.layered A.decodes σ).bsk

/-- Complete A4 field constancy for every actual selected batch, without choice-transport premises. -/
theorem BatchIso.pieceProfile {A B : FamilyReconstruction (2 * R) ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    familyPieceProfile B (transportPrescription F σ) = familyPieceProfile A σ := by
  apply PieceProfile.eq_of_fields (h.gapProfile σ hA)
  · intro b
    obtain ⟨a, rfl⟩ := (h.spliceMolIso σ hA).e.surjective b
    change (stage1PieceOf 0 B.plain B.layered B.decodes (transportPrescription F σ)).layer _ = _
    rw [h.piece_layer σ hA 0]
    exact congrArg (fun a => (stage1PieceOf 0 A.plain A.layered A.decodes σ).layer a)
      (h.splice_branch_cast σ hA a).symm
  · have hh := h.piece_hinges σ hA 0
    change ((stSt B.skeleton (transportPrescription F σ)).hinges).image
      (gardenBranchCast (h.splice_garden_eq σ hA)) = (stSt A.skeleton σ).hinges
    change ((stSt A.skeleton σ).hinges).image _ = (stSt B.skeleton (transportPrescription F σ)).hinges at hh
    rw [← hh, Finset.image_image]
    have he : (fun a => gardenBranchCast (h.splice_garden_eq σ hA)
        ((h.spliceMolIso σ hA).e a)) = id := funext (h.splice_branch_cast σ hA)
    exact (congrArg (fun f => (stSt A.skeleton σ).hinges.image f) he).trans Finset.image_id
  · exact h.piece_gsk σ hA 0
  · exact h.piece_bsk σ hA 0

end WaveTurbulence.VineA
