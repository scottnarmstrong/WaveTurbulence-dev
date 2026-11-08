/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineOperationSplice
public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
/-! The actual post-splice layers and hinge sets constructed for a
selected-family operation agree through its actual splice branch map. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- B1b-2 (Mk-general form of `operation_spliced_layer`). -/
theorem operation_spliced_layerMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (c : GBranch (stSt A.skeleton σ Mk).G.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk').layer
      (RegRed.coreLayer op.output.layered op.output.data op.output.plain op.output.decodes)
      ((operationSpliceMolIsoMk hF op hT).e c) =
    (stSt A.skeleton σ Mk).layer (RegRed.coreLayer A.layered A.data A.plain A.decodes) c :=
  (congrArg (RegRed.coreLayer op.output.layered op.output.data op.output.plain op.output.decodes)
    (operationSpliceMolIso_branch_namesMk hF op hT c)).trans (operation_coreLayer op ((stSt A.skeleton σ Mk).M.ob c))

/-- The actual spliced inherited layer commutes with the actual operation's quotient map. -/
theorem operation_spliced_layer {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).layer
      (RegRed.coreLayer op.output.layered op.output.data op.output.plain op.output.decodes)
      ((operationSpliceMolIso hF op).e c) =
    (stSt A.skeleton σ).layer (RegRed.coreLayer A.layered A.data A.plain A.decodes) c :=
  operation_spliced_layerMk hF op (Stage1Mk.markTransported_empty _) c

/-- Actual hinge membership is preserved, with no extra hinge-compatibility premise. -/
theorem operationSpliceMolIso_hinge_iff {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (operationSpliceMolIso hF op).e c ∈ (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).hinges ↔
      c ∈ (stSt A.skeleton σ).hinges := by
  let S := stSt A.skeleton σ
  let T := stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)
  let F := operationMolIso op
  let E := operationSpliceMolIso hF op
  have he : T.cls (T.M.ob (E.e c)) = (S.cls (S.M.ob c)).map F.e :=
    (congrArg T.cls (operationSpliceMolIso_branch_names hF op c)).trans
      (operation_splice_classes hF op (S.M.ob c))
  have hn : ((S.cls (S.M.ob c)).map F.e ≠ none) ↔ S.cls (S.M.ob c) ≠ none := by
    cases S.cls (S.M.ob c) <;> simp
  exact (T.mem_hinges (E.e c)).trans
    ((Iff.of_eq (congrArg (fun o : Option (GBranch op.output.skeleton.tree) => o ≠ none) he)).trans
      (hn.trans (S.mem_hinges c).symm))

/-- The complete actual constructed hinge sets correspond by the actual quotient atom map. -/
theorem operationSpliceMolIso_hinges_image {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    (stSt A.skeleton σ).hinges.image (operationSpliceMolIso hF op).e =
      (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).hinges := by
  ext y
  obtain ⟨x, rfl⟩ := (operationSpliceMolIso hF op).e.surjective y
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := Finset.mem_image.mp h
    exact (operationSpliceMolIso_hinge_iff hF op x).mpr ((operationSpliceMolIso hF op).e.injective he ▸ hc)
  · intro h
    exact Finset.mem_image.mpr ⟨x, (operationSpliceMolIso_hinge_iff hF op x).mp h, rfl⟩

/-- The actual number of spliced units/hinges is invariant under every selected operation. -/
theorem operation_hinges_card {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    (stSt A.skeleton σ).hinges.card =
      (stSt op.output.skeleton (transportPrescription (operationMolIso op) σ)).hinges.card :=
  (Finset.card_image_of_injective _ (operationSpliceMolIso hF op).e.injective).symm.trans
    (congrArg Finset.card (operationSpliceMolIso_hinges_image hF op))

/-- B1b-2 (Mk-general form of `operation_piece_layer`). -/
theorem operation_piece_layerMk {R d : ℕ} {A : FamilyReconstruction (2 * R) ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (c : GBranch (stSt A.skeleton σ Mk).G.tree) :
    (stage1PieceOf d op.output.plain op.output.layered op.output.decodes
      (transportPrescription (operationMolIso op) σ) Mk').layer ((operationSpliceMolIsoMk hF op hT).e c) =
      (stage1PieceOf d A.plain A.layered A.decodes σ Mk).layer c := operation_spliced_layerMk hF op hT c

/-- The literal layer field of stage1PieceOf is preserved through the actual operation map. -/
theorem operation_piece_layer {R d : ℕ} {A : FamilyReconstruction (2 * R) ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (stage1PieceOf d op.output.plain op.output.layered op.output.decodes
      (transportPrescription (operationMolIso op) σ)).layer ((operationSpliceMolIso hF op).e c) =
      (stage1PieceOf d A.plain A.layered A.decodes σ).layer c :=
  operation_piece_layerMk hF op (Stage1Mk.markTransported_empty _) c

/-- The literal Cs.hinges field of stage1PieceOf is preserved through the actual operation map. -/
theorem operation_piece_hinges {R d : ℕ} {A : FamilyReconstruction (2 * R) ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    ((stage1PieceOf d A.plain A.layered A.decodes σ).Cs.hinges).image (operationSpliceMolIso hF op).e =
      (stage1PieceOf d op.output.plain op.output.layered op.output.decodes
        (transportPrescription (operationMolIso op) σ)).Cs.hinges := operationSpliceMolIso_hinges_image hF op

/-- The literal constructed hinge count is invariant for the actual Stage 1 pieces. -/
theorem operation_piece_hinges_card {R d : ℕ} {A : FamilyReconstruction (2 * R) ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    (stage1PieceOf d A.plain A.layered A.decodes σ).Cs.hinges.card =
      (stage1PieceOf d op.output.plain op.output.layered op.output.decodes
        (transportPrescription (operationMolIso op) σ)).Cs.hinges.card := operation_hinges_card hF op

/-- B1b-2 (Mk-general form of `operation_piece_bsk`). -/
theorem operation_piece_bskMk {R d : ℕ} {A : FamilyReconstruction (2 * R) ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk') :
    (stage1PieceOf d op.output.plain op.output.layered op.output.decodes
      (transportPrescription (operationMolIso op) σ) Mk').bsk =
      (stage1PieceOf d A.plain A.layered A.decodes σ Mk).bsk := bskOf_operationMk hF op hT

/-- The literal bad-vine count of the actual Stage 1 piece is invariant. -/
theorem operation_piece_bsk {R d : ℕ} {A : FamilyReconstruction (2 * R) ι} {i : ι}
    {σ : Prescription A.skeleton} (hF : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    (stage1PieceOf d op.output.plain op.output.layered op.output.decodes
      (transportPrescription (operationMolIso op) σ)).bsk =
      (stage1PieceOf d A.plain A.layered A.decodes σ).bsk :=
  operation_piece_bskMk hF op (Stage1Mk.markTransported_empty _)

end WaveTurbulence.VineA
