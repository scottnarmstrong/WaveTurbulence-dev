/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.LevelNest
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.FlatBase
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.FlatMod.LevelNest
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.FlatBase` (sha256 83a712eebd334a62…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # FLAT-MOD (R60), the modulation as a factor of the summand, and the base case

`modPsi b lam Ψ x t u = e^{πiλ u_b} Ψ x t u`: the modulation carried inside the summand.  `lkRaw_modPsi`: `lkRaw R (modPsi b lam Ψ)` is the
`lkRaw` with the factor `Cont.lowModC R lam t τ` in the time integrand (the lower joint of `R` being `b`).
`Lvl.classSumM_base`: with no operative member the modulated class sum of a level is `c ζ lkRaw (modPsi b lam psiBase)`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C
open WaveTurbulence.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C
variable {γF : ℝ}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS2 WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
  WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont

variable {w : ℕ} {G : Garden w} {d : ℕ}

variable {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- **Base case, modulated**: with no operative member the modulated class sum of a level is the modulated native kernel. -/
theorem LvlΓ.classSumM_base (lam : ℝ) (κ0 : KPar d) (hprime : IsPrimeGarden G) (lv : LvlΓ B)
    (hno : ∀ j, IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    LvlΓ.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam lv κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base (modPsi b lam (lv.psiBase B RD hG layer hLayer κ0)) ![t0, t1, t2] ![e, f, g, h] := by
  classical
  have hp' : IsPrimeGarden (lv.state B RD hG layer hLayer).skeleton := hprime
  unfold LvlΓ.classSumM
  rw [canonFinset_of_noop (lv.state B RD hG layer hLayer) hp' lv.c hno, Finset.sum_singleton]
  unfold twistedLocalKernelM
  exact clLocalKernelModC_eq_lkRaw _ _ lv.region lv.hcb lam _ _ _ _ _ _ _ _ _ _ _ _ _ _

end WaveTurbulence.GammaLow.Famb.VineEstS5C
