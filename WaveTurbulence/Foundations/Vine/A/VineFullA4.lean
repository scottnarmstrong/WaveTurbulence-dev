/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineActualCollection
/-! S2 producer exports: fixed-sigma A4 including actual C1 supports and counts. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist

/-- A4's kernel profile together with the entire actual C1 support set and its actual index count. -/
structure FullA4Profile (w : ℕ) where
  piece : PieceProfile w
  collection : Finset (Finset (Fin w × TTree.Path))
  count : ℕ

namespace PrescribedPrimeGarden
variable {R p : ℕ} {kind : Bool}

/-- Full data of the actual successor piece, independent of a trace or representative choices. -/
noncomputable def fullProfile (a : PrescribedPrimeGarden (2 * R)) : FullA4Profile (2 * R) :=
  ⟨a.profile, collectionAddressSupports a.prime.skeleton a.totalSigma, (a.normalizedPiece 0).Cs.count⟩

end PrescribedPrimeGarden
end WaveTurbulence.VineA
