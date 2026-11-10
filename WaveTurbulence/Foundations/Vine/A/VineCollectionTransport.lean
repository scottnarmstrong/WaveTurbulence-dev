/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCollectionNormalForm
/-! Actual collection supports and Cs counts transport along selected LF batches. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- B1b-2 (Mk-general form of `BatchIso.splice_repC`). -/
theorem BatchIso.splice_repCMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (z : GBranch A.skeleton.tree) :
    repC (stSt B.skeleton (transportPrescription F σ) Mk').cls (F.e z) =
      F.e (repC (stSt A.skeleton σ Mk).cls z) := by
  unfold repC
  rw [h.splice_classesMk σ hT hA z]
  cases (stSt A.skeleton σ Mk).cls z <;> rfl

/-- B1b-2 (Mk-general form of `BatchIso.splice_pi`). -/
theorem BatchIso.splice_piMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (z : GBranch A.skeleton.tree) :
    (h.spliceMolIsoMk σ hT hA).e ((stSt A.skeleton σ Mk).M.pi (stSt A.skeleton σ Mk).hcls z) =
      (stSt B.skeleton (transportPrescription F σ) Mk').M.pi
        (stSt B.skeleton (transportPrescription F σ) Mk').hcls (F.e z) := by
  apply (stSt B.skeleton (transportPrescription F σ) Mk').M.ob_inj
  rw [h.spliceMolIso_branch_namesMk σ hT hA, SpMap.ob_pi, SpMap.ob_pi, h.splice_repCMk σ hT hA z]

end WaveTurbulence.VineA
