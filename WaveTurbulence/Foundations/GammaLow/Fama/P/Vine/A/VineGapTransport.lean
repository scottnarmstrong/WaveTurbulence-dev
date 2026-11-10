/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineGapTransport` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.Vine.A.VineGapTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Famb.Molecule.TwistSourceFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
/-! VINE-A2: exact decorated gap transport of actual ordinary/hyper objects
under the molecular atom/dart isomorphism, retaining the designated deleted bond. -/
@[expose] public section
open WaveTurbulence.Induct WaveTurbulence.GammaLow.FinalCount
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount
variable {V V' D D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]
  [DecidableEq V'] [Fintype D'] [DecidableEq D']
  {M : Molecule V D} {N : Molecule V' D'}


/-- Transport the actual shape and, for a hyper-object, its actual deleted bond. -/
def mapShape (γ : ℝ) [Fact (γ ≤ 1 / 2)] (F : MolIso M N) {S : Finset V} {a b : V} (C : Src.VineLikeObject γ M S a b) :
    Src.VineLikeObject γ N (F.img S) (F.e a) (F.e b) := by
  cases C with
  | vc h => exact .vc (MolIso.isVC_img F h)
  | hyper R => exact .hyper ⟨F.d R.added, F.ends_img R.ends_eq, MolIso.isVC_img (F.erase R.added) R.adjoint⟩

/-- The map of a designated object keeps its designation; it does not rechoose one. -/
def mapObject (γ : ℝ) [Fact (γ ≤ 1 / 2)] (F : MolIso M N) (O : Src.Object γ M) : Src.Object γ N where
  atoms := F.img O.atoms
  upper := F.e O.upper
  lower := F.e O.lower
  shape := mapShape γ F O.shape

/-- Ordered gaps of transported shape data agree for corresponding decorations. -/
theorem mapShape_gap (F : MolIso M N) {S : Finset V} {a b : V} (C : Src.VineLikeObject γ M S a b)
    {d : ℕ} (L : ℝ) (base : Mom d) (κ : D' → (Fin d → ℤ)) (r : Mom d) :
    (mapShape γ F C).IsGap L base κ r ↔ C.IsGap L base (κ ∘ F.d) r := by
  cases C with
  | vc h => exact blockGap_transport F L base κ S a r
  | hyper R => exact blockGap_transport (F.erase R.added) L base (fun x => κ x.1) S a r

/-- Consequently every SG/LG/ZG predicate agrees, including the hyper-adjoint case. -/
theorem mapObject_gapKind (F : MolIso M N) (O : Src.Object γ M) {d : ℕ}
    (L γ' η : ℝ) (base : Mom d) (κ : D' → (Fin d → ℤ)) (k : Molecule.GapKind) :
    (mapObject γ F O).HasGapKind L γ' η base κ k ↔ O.HasGapKind L γ' η base (κ ∘ F.d) k := by
  constructor
  · rintro ⟨r, hr, hk⟩
    exact ⟨r, (mapShape_gap F O.shape L base κ r).mp hr, hk⟩
  · rintro ⟨r, hr, hk⟩
    exact ⟨r, (mapShape_gap F O.shape L base κ r).mpr hr, hk⟩

end WaveTurbulence.GammaLow.Fama.VineA
