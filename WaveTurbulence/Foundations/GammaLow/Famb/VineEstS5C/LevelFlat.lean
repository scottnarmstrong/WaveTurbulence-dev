/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelFlat
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelFlat` (sha256 db7b43e4150368b4…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # Flattening one level of the induction over the core vines (V5 Step 4d part C, WP-I)

`PsiT`: abstract clock-based summands.  `psiStepSp κ0 A sp hprime Ψ'`: the summand of the split `sp` below which the lower factor
has the summand `Ψ'` (`psiSB` of the restricted decoration times `Ψ'` of the decoration restricted to the support of the lower block,
at the exterior times `(u b, t1, t2)`).  `glueFactors_psiStepSp`, **`flat_merge`**: the S-side with the bundle and a lower factor
`c ζ lkRaw Ψ'` is `c ζ lkRaw (psiStepSp Ψ')` of the whole region (via `lkRaw_split_fubini`; hypotheses: clock locality of the bundle and of `Ψ'`,
absolute convergence of the glued summands).  **`Lvl.classSum_flat_step`**: the class sum of a level is `c ζ lkRaw R (Lvl.psiStep Ψ')` given
the same for the next level.
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

variable {w : ℕ} {G : Garden w} {d : ℕ} {p : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {pstar : ι} {J : Set ι}

section LvlStep
variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The summand of a level below which the lower level has the summand `Ψ'`. -/
noncomputable def LvlΓ.psiStep (κ0 : KPar d) (lv : LvlΓ B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hprime : IsPrimeGarden G) (Ψ' : PsiT G d) : PsiT G d :=
  psiStepSp (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime Ψ'

end LvlStep

end WaveTurbulence.GammaLow.Famb.VineEstS5C
