/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.HFree
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.HFree.Ready
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.HFree
-- L5b port of `WaveTurbulence.Foundations.VineEst.HFree.Ready` (sha256 654921d7b3e059ff…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # W2-HFREE (1): operativity at the start state, placement uniqueness

`lvOp_iff`: a member `j` of a level is operative at the level state iff `e j` is operative at the start state
(every level state is a restriction of the start state, with the same layered garden and reconstruction data).
`topOp_of_ready`: canonical + source-layer eligible + both coherences give an operation (identity construction).
`placement_unique`: two placements at the same atoms and lower joint are equal.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.P4.Bot WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.Bot

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- A core member is operative at the start state. -/
def TopOpΓ (i : (assemblySourceFamilyΓ B).CoreIndex) : Prop :=
  Nonempty (FamilyOperation (p := p) (kind := kind) (startStateΓ B RD hG layer hLayer) i)

theorem lvOp_iffΓ (lv : LvlΓ B) (j : lv.ι) :
    lv.Op (p := p) (kind := kind) B RD hG layer hLayer j ↔ TopOpΓ (p := p) (kind := kind) B RD hG layer hLayer (lv.e j) :=
  ⟨fun ⟨op⟩ => ⟨opOfRestrict _ lv.e lv.he op⟩, fun ⟨op⟩ => ⟨opToRestrict _ lv.e lv.he op⟩⟩

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
