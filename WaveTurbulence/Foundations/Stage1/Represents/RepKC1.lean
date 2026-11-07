/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVN12
import Mathlib.Tactic

/-!
# S2 REPRESENTS: V5-KIND continuity (`hcont`) for the unit class kernels

`unit_hcont` discharges the `hcont` input of `exists_hinge_data_units` with V5-CONT's kind-generic
`twistedRecenteredModC_continuousOn` (uni-kind, `VineEstS5C/Cont/ModClass.lean`), for a unit of an `IsCanonGC` garden.
The hypotheses are the Part-I parameter facts of the `WTPrefix` and the two leafwise gates (as for V5's own export).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract TTree WaveTurbulence.LGSpine
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3.FS
open scoped ENNReal

theorem unit_hcont {P : WTParams} (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) (h : ℕ → Mom P.d → ℝ) (bb : ℝ)
    (hh : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal bb)
    {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℤ) :
    ∀ E ∈ outSet (unitD hM9 B RD hG layer hLayer centre wBar) P.L P.γ P.η,
      ContinuousOn (fun t => unitHk P p B RD hG layer hLayer h wBar lam t (sumintBoundary (G.sign a.toNode) E))
        (cubeSet (unitD hM9 B RD hG layer hLayer centre wBar).qOut) := by
  have hB : ProfileBound P h (fun _ => max bb 1) p := fun r hr =>
    ⟨le_max_of_le_right zero_le_one,
      (hh r hr).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  exact WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC_continuousOn (kind := objKind w) (lam : ℝ) hgate hinc hd
    hη0 hη6 hη2 hC hδ hL hw hp hB (fun r _ => lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hprime hM9 B RD hG
    layer hLayer (fun x => WaveTurbulence.Canon.layer_le_of_isCanonGC hcan x) hord centre wBar
    (rowCoherent_of_canonical hM9 B RD hG layer hLayer p hcan centre wBar P.L P.γ P.δ h)

end WaveTurbulence.Represents
