/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Flat
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModClass
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Export
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelTop
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.FlatMod.Flat
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Export` (sha256 90c76d27decb6afd…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # FLAT-MOD (R60), export

`Lvl.top_classSumM`: the modulated class sum of the top level is the sum over `canonFinset` of the member kernels of
`Cont.twistedRecenteredModC` (definitional).  **`twistedRecenteredModC_eq_flat`**: `twistedRecenteredModC` of the start class is the
recentering factor times `c ζ lkRaw (modPsi b λ psiFuel)`.  `modPsi_zero`, `classSum_eq_flat_of_flatM`: `λ = 0` recovers
`Lvl.classSum_eq_flat`.
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
  WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem LvlΓ.top_classSumM (lam : ℝ) (κ0 : KPar d) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    LvlΓ.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam (LvlΓ.top B) κ0 t0 t1 t2 e f g h =
      ∑ z ∈ canonFinsetK p kind (startStateΓ B RD hG layer hLayer) (chainStartΓ B),
        clLocalKernelModC z.1.data z.1.plain (clRegionData z.1.skeleton z.2.block z.2.cl) κ0.L κ0.γ κ0.δ κ0.F
          (stateLayer z.1) (stateLayer_isLayering z.1) κ0.base lam t0 t1 t2 e f g h := rfl

/-- **FLAT-MOD export**: the modulated class kernel `twistedRecenteredModC` of the start class is the recentering factor times
`c ζ lkRaw (modPsi b λ psiFuel)` (`b` the lower joint of the chain; `modPsi b λ Ψ x t u = e^{πiλ u_b} Ψ x t u`). -/
theorem twistedRecenteredModC_eq_flatΓ (hprime : IsPrimeGarden G) (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    twistedRecenteredModC G a (canonFinsetK p kind (startStateΓ B RD hG layer hLayer) (chainStartΓ B))
        κ0.L κ0.γ κ0.δ κ0.F κ0.base lam t0 t1 t2 e f g h =
      Complex.exp (((-(Real.pi * κ0.δ * κ0.L ^ (2 * κ0.γ)) * t0 * boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) *
        Complex.I) *
      ((coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (LvlΓ.top B).region * clLocalZeta (LvlΓ.top B).region *
        lkRaw (LvlΓ.top B).region κ0.L κ0.base
          (modPsi b lam (LvlΓ.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime
            (Fintype.card (LvlΓ.top B).ι + 1) (LvlΓ.top B))) ![t0, t1, t2] ![e, f, g, h]) := by
  rw [← LvlΓ.classSumM_eq_flatM (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime (LvlΓ.top B) t0 t1 t2 e f g h,
    LvlΓ.top_classSumM]
  rfl

end WaveTurbulence.GammaLow.Famb.VineEstS5C
