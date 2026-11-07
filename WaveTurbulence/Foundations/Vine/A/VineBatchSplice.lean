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

/-- The actual composed batch map transports every actual merge class. -/
theorem BatchIso.splice_classes (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) (b : GBranch A.skeleton.tree) :
    (stSt B.skeleton (transportPrescription F σ)).cls (F.e b) =
      ((stSt A.skeleton σ).cls b).map F.e := by
  induction h with
  | nil A =>
    rw [transportPrescription_refl]
    change (stSt A.skeleton σ).cls b = ((stSt A.skeleton σ).cls b).map id
    cases (stSt A.skeleton σ).cls b <;> rfl
  | skip _ _ ih => exact ih σ hA b
  | @apply L A B i op J h ih =>
    have hh := ih (transportPrescription (operationMolIso op) σ)
      (isV0Fam_operation hA op) ((operationMolIso op).e b)
    rw [transportPrescription_trans, operation_splice_classes hA op b] at hh
    simpa only [Option.map_map, molIsoTrans, Equiv.coe_trans, Function.comp_def] using hh

/-- The actual batch induces a molecular map between the actual constructed splices. -/
noncomputable def BatchIso.spliceMolIso (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    MolIso (stSt A.skeleton σ).G.molecule
      (stSt B.skeleton (transportPrescription F σ)).G.molecule :=
  quotientMolIso F (h.splice_classes σ hA) (stSt A.skeleton σ).M
    (stSt B.skeleton (transportPrescription F σ)).M

/-- The actual batch splice map keeps the actual original-branch names. -/
theorem BatchIso.spliceMolIso_branch_names (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (stSt B.skeleton (transportPrescription F σ)).M.ob ((h.spliceMolIso σ hA).e c) =
      F.e ((stSt A.skeleton σ).M.ob c) :=
  quotientBranchEquiv_comm F (h.splice_classes σ hA) _ _ c

/-- The actual batch splice map keeps the actual original-dart names. -/
theorem BatchIso.spliceMolIso_dart_names (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) (x : GardenDart (stSt A.skeleton σ).G) :
    (stSt B.skeleton (transportPrescription F σ)).M.od ((h.spliceMolIso σ hA).d x) =
      F.d ((stSt A.skeleton σ).M.od x) :=
  quotientDartEquiv_comm F (h.splice_classes σ hA) _ _ x

end WaveTurbulence.VineA
