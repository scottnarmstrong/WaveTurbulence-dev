/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcMom2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRegion
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelTop
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRegion` (sha256 e15a63f0fa7fa517…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 17): the region data of a block is unique; `(Lvl.top B).region = R`

`clRegionData_ext`: two `CLRegionData G U a b` are equal (the slots `kept`, `positive`, `negative` agree for nested blocks with the same lower joint, `region_lower_eq_of_subset`,
and `excluded` is determined by `upper`).  `top_region_eq`: the region of the top level is the region of the chain assembly, so `TermCertW .. (Lvl.top B)` can be proved with the
engine assembly `B` itself (`rw [top_region_eq B]` in the goal).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

variable {R : CLRegionData G U a b} {n : ℕ}

theorem top_region_eqΓ (B : CLChainAssemblyΓ γF G R n) : (LvlΓ.top B).region = R := clRegionData_ext _ _

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
