/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BotAbs4
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs2
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs3
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.AbsBase2
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelAbs3` (sha256 5a929bb9036aeda5…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # The flat identity of the induction over the core vines, with no named hypothesis (V5 Step 4d part C)

`Lvl.absLeaves`: all leaf obligations of `hAbs` (`sb`, `sbm`, `base`, `basem`, `bot`, `botm`) hold.  **`Lvl.classSum_eq_flat`**: for every level, the class
sum is `c ζ lkRaw` of the recursively defined summand `psiFuel` (the flat form of TARGET Step 4, with the bottom vine handled by 4d-B2).
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

/-- **All leaf obligations of `hAbs` hold.** -/
theorem LvlΓ.absLeaves (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (hprime : IsPrimeGarden G) :
    AbsLeavesΓ (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime where
  sb := fun lv pstar hk => sAbs_psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime hL hF
  sbm := fun lv pstar hk x => measurable_psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer)
    (lv.split B RD hG layer hLayer pstar hk) hprime hF x
  base := fun lv => (LvlΓ.abs_base B RD hG layer hLayer κ0 hL hF lv).1
  basem := fun lv => (LvlΓ.abs_base B RD hG layer hLayer κ0 hL hF lv).2
  bot := fun lv pstar h0 hup => uAbs_psiBot (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) lv.c hprime
    (LvlΓ.bottom_hb0 B RD hG layer hLayer lv pstar h0) hup hL hF
  botm := fun lv pstar h0 hup => measT_psiBot κ0 (lv.state B RD hG layer hLayer) lv.c hF

end WaveTurbulence.GammaLow.Famb.VineEstS5C
