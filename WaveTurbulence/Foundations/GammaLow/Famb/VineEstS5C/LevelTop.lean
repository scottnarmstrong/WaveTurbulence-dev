/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelLoc2
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelLoc2
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelTop` (sha256 fe3e073673716a8b…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The top level of the induction over the core vines (V5 Step 4d part C, WP-I)

`Lvl.top`: all core members and the whole chain region of the assembly; `Lvl.top_classSum`: its class sum is the sum over `canonFinset`
of the start state of `twistedLocalKernel` (definitional), i.e. the left-hand side of `VineEstCanon` up to the recentering factor.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The top level: all core members, the whole chain region. -/
noncomputable def LvlΓ.top : LvlΓ B where
  ι := (assemblySourceFamilyΓ B).CoreIndex
  e := id
  he := Function.injective_id
  k0 := n
  hk0 := le_refl _
  hmem := fun j => j.1.2
  hsurj := fun i _ => ⟨i, rfl⟩
  c := chainStartΓ B
  hcU := (iregion_fullΓ B).symm
  hca := (jointAt_topΓ B).symm
  hcb := rfl

end WaveTurbulence.GammaLow.Famb.VineEstS5C
