/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePlainA4
public import WaveTurbulence.Foundations.Vine.A.VineSpliceDecorationLift
/-! Actual successor collection geometry and hinge semantics on every spliced decoration. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LGSpine LFTwist
variable {w p d : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Full C1 support names in the literal common normalized garden. -/
noncomputable def collectionAddressSupports (G : Garden w) (σ : Prescription G) :
    Finset (Finset (Fin w × TTree.Path)) := by
  classical
  exact ((NormalizedSplice.objects G σ).map (fun O => O.atoms.image Subtype.val)).toFinset

end WaveTurbulence.VineA
