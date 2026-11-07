/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.Flat
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModClass
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelTop

/-! # FLAT-MOD (R60), export

`Lvl.top_classSumM`: the modulated class sum of the top level is the sum over `canonFinset` of the member kernels of
`Cont.twistedRecenteredModC` (definitional).  **`twistedRecenteredModC_eq_flat`**: `twistedRecenteredModC` of the start class is the
recentering factor times `c ζ lkRaw (modPsi b λ psiFuel)`.  `modPsi_zero`, `classSum_eq_flat_of_flatM`: `λ = 0` recovers
`Lvl.classSum_eq_flat`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory
  WaveTurbulence.VineEstS5C.FlatMod WaveTurbulence.VineEstS5C.Cont

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem Lvl.top_classSumM (lam : ℝ) (κ0 : KPar d) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    Lvl.classSumM (p := p) (kind := kind) B RD hG layer hLayer lam (Lvl.top B) κ0 t0 t1 t2 e f g h =
      ∑ z ∈ canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B),
        clLocalKernelModC z.1.data z.1.plain (clRegionData z.1.skeleton z.2.block z.2.cl) κ0.L κ0.γ κ0.δ κ0.F
          (stateLayer z.1) (stateLayer_isLayering z.1) κ0.base lam t0 t1 t2 e f g h := rfl

/-- **FLAT-MOD export**: the modulated class kernel `twistedRecenteredModC` of the start class is the recentering factor times
`c ζ lkRaw (modPsi b λ psiFuel)` (`b` the lower joint of the chain; `modPsi b λ Ψ x t u = e^{πiλ u_b} Ψ x t u`). -/
theorem twistedRecenteredModC_eq_flat (hprime : IsPrimeGarden G) (lam : ℝ) (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    twistedRecenteredModC G a (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        κ0.L κ0.γ κ0.δ κ0.F κ0.base lam t0 t1 t2 e f g h =
      Complex.exp (((-(Real.pi * κ0.δ * κ0.L ^ (2 * κ0.γ)) * t0 * boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) *
        Complex.I) *
      ((coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (Lvl.top B).region * clLocalZeta (Lvl.top B).region *
        lkRaw (Lvl.top B).region κ0.L κ0.base
          (modPsi b lam (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime
            (Fintype.card (Lvl.top B).ι + 1) (Lvl.top B))) ![t0, t1, t2] ![e, f, g, h]) := by
  rw [← Lvl.classSumM_eq_flatM (p := p) (kind := kind) B RD hG layer hLayer lam κ0 hL hF hprime (Lvl.top B) t0 t1 t2 e f g h,
    Lvl.top_classSumM]
  rfl

theorem modPsi_zero (b : GBranch G.tree) (Ψ : PsiT G d) : modPsi b 0 Ψ = Ψ := by
  funext x t u
  simp [modPsi]

/-- λ = 0: the modulated flat identity gives `Lvl.classSum_eq_flat`. -/
theorem Lvl.classSum_eq_flat_of_flatM (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (hprime : IsPrimeGarden G)
    (lv : Lvl B) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 lv.region * clLocalZeta lv.region *
        lkRaw lv.region κ0.L κ0.base
          (Lvl.psiFuel (p := p) (kind := kind) B RD hG layer hLayer κ0 hprime (Fintype.card lv.ι + 1) lv) ![t0, t1, t2] ![e, f, g, h] := by
  rw [← Lvl.classSumM_zero (p := p) (kind := kind) B RD hG layer hLayer κ0 lv,
    Lvl.classSumM_eq_flatM (p := p) (kind := kind) B RD hG layer hLayer 0 κ0 hL hF hprime lv, modPsi_zero]

end WaveTurbulence.VineEstS5C
