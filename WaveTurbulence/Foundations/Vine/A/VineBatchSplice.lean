/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePieceIndex
/-! Actual simultaneous-splice quotient maps along selected LF batches. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- B1b-2 (Mk-general form of `BatchIso.splice_classes`). -/
theorem BatchIso.splice_classesMk (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (b : GBranch A.skeleton.tree) :
    (stSt B.skeleton (transportPrescription F σ) Mk').cls (F.e b) =
      ((stSt A.skeleton σ Mk).cls b).map F.e := by
  induction h with
  | nil A =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    rw [transportPrescription_refl]
    change (stSt A.skeleton σ Mk).cls b = ((stSt A.skeleton σ Mk).cls b).map id
    cases (stSt A.skeleton σ Mk).cls b <;> rfl
  | skip _ _ ih => exact ih σ hT hA b
  | @apply L A B i op J h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) J hT
    have hh := ih (transportPrescription (operationMolIso op) σ) h2
      (isV0Fam_operationMk hA op h1) ((operationMolIso op).e b)
    rw [transportPrescription_trans, operation_splice_classesMk hA op h1 b] at hh
    simpa only [Option.map_map, molIsoTrans, Equiv.coe_trans, Function.comp_def] using hh

/-- The actual composed batch map transports every actual merge class. -/
theorem BatchIso.splice_classes (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) (b : GBranch A.skeleton.tree) :
    (stSt B.skeleton (transportPrescription F σ)).cls (F.e b) =
      ((stSt A.skeleton σ).cls b).map F.e := h.splice_classesMk σ (Stage1Mk.markTransported_empty F) hA b

/-- B1b-2 (Mk-general form of `BatchIso.spliceMolIso`). -/
noncomputable def BatchIso.spliceMolIsoMk (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) :
    MolIso (stSt A.skeleton σ Mk).G.molecule
      (stSt B.skeleton (transportPrescription F σ) Mk').G.molecule :=
  quotientMolIso F (h.splice_classesMk σ hT hA) (stSt A.skeleton σ Mk).M
    (stSt B.skeleton (transportPrescription F σ) Mk').M

/-- The actual batch induces a molecular map between the actual constructed splices. -/
noncomputable def BatchIso.spliceMolIso (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    MolIso (stSt A.skeleton σ).G.molecule
      (stSt B.skeleton (transportPrescription F σ)).G.molecule :=
  h.spliceMolIsoMk σ (Stage1Mk.markTransported_empty F) hA

/-- B1b-2 (Mk-general form of `BatchIso.spliceMolIso_branch_names`). -/
theorem BatchIso.spliceMolIso_branch_namesMk (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (c : GBranch (stSt A.skeleton σ Mk).G.tree) :
    (stSt B.skeleton (transportPrescription F σ) Mk').M.ob ((h.spliceMolIsoMk σ hT hA).e c) =
      F.e ((stSt A.skeleton σ Mk).M.ob c) :=
  quotientBranchEquiv_comm F (h.splice_classesMk σ hT hA) _ _ c

/-- The actual batch splice map keeps the actual original-branch names. -/
theorem BatchIso.spliceMolIso_branch_names (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (stSt B.skeleton (transportPrescription F σ)).M.ob ((h.spliceMolIso σ hA).e c) =
      F.e ((stSt A.skeleton σ).M.ob c) := h.spliceMolIso_branch_namesMk σ (Stage1Mk.markTransported_empty F) hA c

/-- B1b-2 (Mk-general form of `BatchIso.spliceMolIso_dart_names`). -/
theorem BatchIso.spliceMolIso_dart_namesMk (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (x : GardenDart (stSt A.skeleton σ Mk).G) :
    (stSt B.skeleton (transportPrescription F σ) Mk').M.od ((h.spliceMolIsoMk σ hT hA).d x) =
      F.d ((stSt A.skeleton σ Mk).M.od x) :=
  quotientDartEquiv_comm F (h.splice_classesMk σ hT hA) _ _ x

/-- The actual batch splice map keeps the actual original-dart names. -/
theorem BatchIso.spliceMolIso_dart_names (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) (x : GardenDart (stSt A.skeleton σ).G) :
    (stSt B.skeleton (transportPrescription F σ)).M.od ((h.spliceMolIso σ hA).d x) =
      F.d ((stSt A.skeleton σ).M.od x) := h.spliceMolIso_dart_namesMk σ (Stage1Mk.markTransported_empty F) hA x

end WaveTurbulence.VineA
