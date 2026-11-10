/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ModStatement
public import WaveTurbulence.Foundations.Vine.DegenVine.MixAlgebra
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.FlatMod.FlatBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRecurse
public import WaveTurbulence.Foundations.VineEst.VineEstS5B2.Bot8
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Trunc
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P2.Recentered
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P3.Bound
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GenMerge
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelRec

/-! Definitions-only split of the V5-SPACE (kind-generic) statement layer: the member and class kernels with a spatial
multiplier inside each lattice sum (`memberMX`, `twistedRecenteredModCX`), the engine pullback (`EnginePullback`), the
node weight (`nodeWeight`), the spatial multiplier on a recentered family (`spatialMul`) and the weighted flat observable
(`flatFnRMX`).  Bodies are verbatim from V5-SPACE (`VineSpaceK.Kernel`, `Certificate`, `NodeWeight`, `Engine`,
`FlatBound`); the proof modules there will import this module and drop their copies when V5-SPACE lands. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.VineSpaceK
section KernelDefs
open MeasureTheory VineEstS5C VineEstS5C.Cont VineEstS4 LFTwist RegRed Reg.Skeleton
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

abbrev ClassMember (w : ℕ) (ι : Type*) := Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family

end KernelDefs

section CertificateDefs
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3
  VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract
  VineEstS2 VineEstS3 VineEstS4 TTree
open scoped ENNReal
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Every possible witness assembly must realize the SAME node multiplier, with
frequencies fixed before the input sum and one common mass budget. This is algebraic
Fourier data; the only inequality is its presentation mass. -/
def EnginePullback (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (mass : ℝ) : Prop :=
  ∀ (n : ℕ) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hL : L ≠ 0),
  ∃ N : CharMix (assemblyShape hM9 B) d, N.mass ≤ mass ∧
    ∀ (β : Fin 4 → Fin d → ℤ) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      m (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) =
        N.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x

end CertificateDefs

section NodeWeightDefs
open Classical TTree Twist RegRed VineEstS4 VineEstS5B VineEstS5B2
variable {w d : ℕ} {G : Garden w}

def nodeWeight (W : (Fin 4 → Mom d) → ℂ) (L : ℝ) (base : Mom d)
    (v : GBranch G.tree) (x : GNode G.tree → Fin d → ℤ) : ℂ :=
  W ![cosetDecoration G L base x v.toNode,
      cosetDecoration G L base x (v.child 0),
      cosetDecoration G L base x (v.child 1),
      cosetDecoration G L base x (v.child 2)]

end NodeWeightDefs

section EngineDefs
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3
  VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract
  VineEstS2 VineEstS3 VineEstS4 TTree
open scoped ENNReal
variable {w d : ℕ} {G : Garden w}

def spatialMul (m : (GNode G.tree → Fin d → ℤ) → ℂ) (ψ : PsiT G d) : PsiT G d :=
  fun x tt u => m x * ψ x tt u

end EngineDefs

section FlatDefs
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal

open VineEstS5C.P4.Final
variable {kind : Bool}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
  {d : ℕ} {p : ℕ}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)


end FlatDefs

end WaveTurbulence.VineSpaceK
