/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Class
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Prefix

/-! # TARGET Proposition `vineest` (L1730-L1752), the full statement with the LF-twist sum (V5 Step 4a)

`VineEstFull P` is `Step3Statement P` with the single-garden kernel `K̃^U_{(G)}` replaced by
`K̃^U = e^{-πiδL^{2γ}t_{u1}Γ} Σ_{G'} K^U_{(G')}` (vineest1), the sum over the gardens `G'` of the twist class (LF twists
of `G` at the chain `U`, `allCoreOutputs` of the core family of its pieces).  The premise `CoreVinesNoTwist` of Step 3
is removed (it is the case in which the class is a singleton, `BaseCase`).

The summand of a garden is the kernel of one representative state reached by a batch (`ClassSection`).  The statement
holds for every choice of representatives, so no independence of the representative is assumed; the sections exist
(`exists_classSection`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  VineParamContract TTree
open scoped ENNReal

/-- (vineest1): `e^{-πiδL^{2γ}t_{u1}Γ} Σ_{G'} K^U_{(G')}`, the sum over the representatives `Z` of the twist class. -/
@[expose] noncomputable def twistedRecentered {w d : ℕ} {ι : Type*} (G : Garden w) (a : GBranch G.tree)
    (Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family))
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tUpper * boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) *
    Complex.I) *
    ∑ x ∈ Z, twistedLocalKernel x.1 x.2 L γ δ F base tUpper tPositive tNegative e f g h

/-- **TARGET Proposition `vineest` (L1730-L1752), full statement.**  Same binders and bound as `Step3Statement`, without
the case premise `CoreVinesNoTwist`; the kernel is (vineest1), summed over any set of representatives `Z` of the twist
class of the chain `U` of `G` (`ClassSection`). -/
@[expose] def VineEstFull (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ {Rin : ℕ → Mom P.d → ℝ}, (∀ r ≤ p, InputRemainder P (Rin r) r) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer), (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ (inputsF P Rin) p →
    ∀ (kind : Bool) (Z : Finset (Σ Bs : FamilyReconstruction w (assemblySourceFamily B).CoreIndex, ChainAt Bs.skeleton Bs.family)),
    ClassSectionK p kind (startState B RD hG layer hLayer) (chainStart B) Z →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecentered G a Z P.L P.γ P.δ (inputsF P Rin) wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7))

end WaveTurbulence.VineEstS4
