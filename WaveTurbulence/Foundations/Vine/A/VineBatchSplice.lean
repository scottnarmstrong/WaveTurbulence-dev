/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineChosenIncoherency
public import WaveTurbulence.Foundations.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeChainLayering
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

/-- B1b-3: the splice state's hinge set (branches with a splice class, `SpState.hinges`) follows the actual batch
map at markings carried by the batch. It reads neither hinge pairs nor the gap specification. -/
theorem BatchIso.splice_hinge_iffMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (c : GBranch (stSt A.skeleton σ Mk).G.tree) :
    (h.spliceMolIsoMk σ hT hA).e c ∈ (stSt B.skeleton (transportPrescription F σ) Mk').hinges ↔
      c ∈ (stSt A.skeleton σ Mk).hinges := by
  let S := stSt A.skeleton σ Mk
  let T := stSt B.skeleton (transportPrescription F σ) Mk'
  have he : T.cls (T.M.ob ((h.spliceMolIsoMk σ hT hA).e c)) = (S.cls (S.M.ob c)).map F.e :=
    (congrArg T.cls (h.spliceMolIso_branch_namesMk σ hT hA c)).trans (h.splice_classesMk σ hT hA (S.M.ob c))
  have hn : ((S.cls (S.M.ob c)).map F.e ≠ none) ↔ S.cls (S.M.ob c) ≠ none := by
    cases S.cls (S.M.ob c) <;> simp
  exact (T.mem_hinges _).trans
    ((Iff.of_eq (congrArg (fun o : Option (GBranch B.skeleton.tree) => o ≠ none) he)).trans
      (hn.trans (S.mem_hinges c).symm))

/-- B1b-3: the complete splice hinge sets correspond by the actual batch quotient map. -/
theorem BatchIso.splice_hinges_imageMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) :
    (stSt A.skeleton σ Mk).hinges.image (h.spliceMolIsoMk σ hT hA).e =
      (stSt B.skeleton (transportPrescription F σ) Mk').hinges := by
  ext y
  obtain ⟨x, rfl⟩ := (h.spliceMolIsoMk σ hT hA).e.surjective y
  constructor
  · intro hy
    obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hy
    exact (h.splice_hinge_iffMk σ hT hA x).mpr ((h.spliceMolIsoMk σ hT hA).e.injective he ▸ hc)
  · intro hy
    exact Finset.mem_image.mpr ⟨x, (h.splice_hinge_iffMk σ hT hA x).mp hy, rfl⟩

end WaveTurbulence.VineA
