/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVineEstM
public import WaveTurbulence.Foundations.Stage1.Represents.RepE1
public import WaveTurbulence.Foundations.Stage1.Represents.RepE2
public import WaveTurbulence.Foundations.Stage1.Represents.RepE3
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-E: VINEEST(λ) for a unit of a canonical garden, premises discharged

`unit_vineest_bound`: for a unit `(U, a, b, R, B)` of the prime skeleton `G` of a canonical layered garden (`IsCanonGC`),
VINEEST (`VineEstCanonLayerHalfMK`, kind `objKind w`) with its `RowCoherent` premise (`rowCoherent_of_canonical`), its
canonicity premise (`canonicalObject_of_isCanonGC`), its layer bound and the order bound `clLocalOrder1 ≤ N₁⁴` (premise `hcl`; `clLocalOrder1_le_N1` from `G.order ≤ N_{p+1}⁴`)
discharged except the order premises: the `XNorm00Restr` bound of the modulated class kernel for every centre and modulation.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C VineParamContract TTree WaveTurbulence.LGSpine
open scoped ENNReal

theorem unit_vineest_bound {P : WTParams} (hV : VineEstCanonLayerHalfMK P) {p : ℕ} (hp : p < P.D)
    (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (hh : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀)
    {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hcan : IsCanonGC (p + 1) (layeredReconstruction RD hG layer hLayer))
    (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hcl : clLocalOrder1 R ≤ P.N 1 ^ 4)
    (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ) :
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => WaveTurbulence.VineEstS5C.Cont.twistedRecenteredModC G a
        (canonFinsetK p (objKind w) (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀))) :=
  hV hp h B₀ hB₀ hh hprime hM9 B RD hG layer hLayer (objKind w) (canonicalObject_of_isCanonGC hcan)
    (fun x => WaveTurbulence.Canon.layer_le_of_isCanonGC hcan x) hord hcl centre wBar lam
    (rowCoherent_of_canonical hM9 B RD hG layer hLayer p hcan centre wBar P.L P.γ P.δ h)

end WaveTurbulence.Represents
