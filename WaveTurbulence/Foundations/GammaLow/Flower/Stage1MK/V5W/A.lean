/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.Flower.V5W.ContCore
public import WaveTurbulence.Foundations.Flower.V5W.Statements
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Engine
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Certificate
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.AffineMixture
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.NativeInverse
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.NormalizedAffine
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceB.Pullback
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyChart
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyCoefficients
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyDecode
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLAssemblyShape
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainAssembly
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLChainCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLClockReindex
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLNormalizedCoordinates
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Momenta
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.CLStep2Time
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.BadClause
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.CohmolBound
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.LayerFacts
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.NativeRows
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3At
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS3.Step3Data
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.Class
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS4.RowCoh
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.LevelRec
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P2.Dict2
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.Free
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.ModStatement

/-! # FLOWER-LOW (packet L8), item I3 (A): the weighted vine estimate (V5W) over `𝒱_γ`

Main's `Flower.V5W*` declarations that depend on the chain assembly or the chart obligation (the cone of
`V5WT.v5FrontierClassBound` through `VineEstS2.CLChainAssembly`, `VINEPARAM`, `ChainPiece`), copied by source
(sha256 in `COPIED-SHA256SUMS`) onto L5b's `𝒱_γ` port of the vine estimate (`GammaLow.Famb`, names suffixed `Γ`),
with L5b's rules: `CLChainAssembly` ↦ `Famb.VineEstS2.CLChainAssemblyΓ γF`, `ChainPiece` ↦ `ChainPieceΓ γF`,
`VINEPARAM` ↦ `Famb.NormalChartSupply γF`, `.vineType` ↦ `.label`; copied names get the suffix `Γ`. Everything else
(weights, frontier filters, flat estimates, kernels) is main's, by import. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.VineSpaceK
open WaveTurbulence.VineParamContract
open MeasureTheory VineEstS5C VineEstS5C.Cont VineEstS4 LFTwist RegRed Reg.Skeleton
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open scoped ENNReal
open Classical TTree Twist RegRed VineEstS4 VineEstS5B VineEstS5B2
open MeasureTheory DegenVine VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 TTree
open scoped ENNReal
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open scoped ENNReal
open VineEstS5C.P4.Final
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- Every possible witness assembly must realize the SAME node multiplier, with
frequencies fixed before the input sum and one common mass budget. This is algebraic
Fourier data; the only inequality is its presentation mass. -/
def EnginePullbackΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (mass : ℝ) : Prop :=
  ∀ (n : ℕ) (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (hL : L ≠ 0),
  ∃ N : CharMix (Famb.VineEstS2.assemblyShapeΓ hM9 B) d, N.mass ≤ mass ∧
    ∀ (β : Fin 4 → Fin d → ℤ) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      m (clExtendIndices R ((Famb.VineEstS2.clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) =
        N.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5W
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory Filter Topology
open WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineC WaveTurbulence.Flower.Stage1W
open scoped ENNReal
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
  (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B) d)

/-- The root parent layers of the incoherent couple row of a `sumint` row are its clock-slot layers. -/
theorem coupleRootParents_rowQΓ (hq : W.q = Famb.VineEstS2.assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (pw : ℕ)
    (v : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx) :
    coupleRootParents pw RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1 0 =
        (Famb.VineEstS3.rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).1 ∧
      coupleRootParents pw RD hG layer hLayer (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).1 1 =
        (Famb.VineEstS3.rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inl v)).2 := by
  rw [Famb.VineEstS4.rowQ_inl_eqΓ hM9 B RD hG layer hLayer W hq hqo L γ δ F v]
  have hp := pairLeaf_ne (a := a) hG (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v)
  have h1 := (clRegionalPair_realization hG _ (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).2).1
  have h2 := (clRegionalPair_realization hG _ (Famb.VineEstS2.assemblyPairOfΓ hM9 B hG v).2).2
  obtain ⟨n1, _⟩ := cl_realization_parent B.isBlock R _ h1 hp.1
  obtain ⟨n2, _⟩ := cl_realization_parent B.isBlock R _ h2 hp.2
  constructor
  · rw [coupleRootParents_zero RD hG layer hLayer pw _ _ _ (Mole.parent_child_eq_node _ n1).symm]
    simp [pairQ, parentCoreLayer, n1]
  · rw [coupleRootParents_one RD hG layer hLayer pw _ _ _ (Mole.parent_child_eq_node _ n2).symm]
    simp [pairQ, parentCoreLayer, n2]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5W
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.DegenVine WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory Filter Topology
open WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineC WaveTurbulence.Flower.Stage1W
open scoped ENNReal
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}
variable (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
  (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B) d)

/-- The root parent layer of the incoherent tree row of a `sumint` row is its first clock-slot layer. -/
theorem treeRootParent_rowQΓ (hq : W.q = Famb.VineEstS2.assemblyTimeQΓ hM9 B (fun v => layer (RD.coreBranch hG v).toNode))
    (hqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (pw : ℕ)
    (v : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx) :
    treeRootParent pw RD hG layer hLayer (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).1 =
      (Famb.VineEstS3.rowQΓ hM9 B RD hG W L γ δ F layer hLayer (Sum.inr v)).1 := by
  rw [Famb.VineEstS4.rowQ_inr_eqΓ hM9 B RD hG layer hLayer W hq hqo L γ δ F v]
  have hbr := (branch_mem_clRealizationNodes (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).1).mpr
    (Finset.mem_erase.mp (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v).2).2
  have hne := interior_ne (Famb.VineEstS2.assemblyBranchOfΓ hM9 B v)
  obtain ⟨hn, _⟩ := cl_realization_parent B.isBlock R _ hbr hne
  rw [treeRootParent_eq RD hG layer hLayer pw _ _ _ (Mole.parent_child_eq_node _ hn).symm]
  simp [branchQ, parentCoreLayer, hn]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5W
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB WaveTurbulence.VineC WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W
open scoped ENNReal FourierTransform
open Set
open VineEstS5C.P4.Final LGSpine Cut2A
variable {γF : ℝ}

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.V5W
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB WaveTurbulence.VineC WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W
open scoped ENNReal FourierTransform
open Set
open VineEstS5C.P4.Final LGSpine Cut2A
variable {γF : ℝ}

end

section
open WaveTurbulence.VineSpaceK
open MeasureTheory DegenVine DegenVinePar VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 VineEstS5C.P4.W2 VineEstS3Par.Eng RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 VineEstS5A TTree
open scoped ENNReal
variable {γF : ℝ}
variable {A : ℝ} {P : WTParams} {D : SumintPar.SumintDatum P.d}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {R : CLRegionData G U a b} {n : ℕ}

/-- Pullback at the actual normalized coordinates. No norm estimate is part of this certificate. -/
theorem freeDict_mulΓ (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (Famb.VineEstS2.assemblyShapeΓ hM9 B) d) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (base : Mom d)
    (β : Fin 4 → Fin d → ℤ) (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (tt : Fin 3 → ℝ)
    (ψ : PsiT G d) (m : (GNode G.tree → Fin d → ℤ) → ℂ)
    (wN wDec : ℕ) (bk : Fin (Famb.VineEstS2.assemblyShapeΓ hM9 B).I → Fin 4)
    (cons : Finset ((Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar × (Famb.VineEstS2.assemblyShapeΓ hM9 B).TVar))
    (g g' : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → ℕ)
    (Mx N : CharMix (Famb.VineEstS2.assemblyShapeΓ hM9 B) d)
    (cr : ClockedRows3 (Famb.VineEstS5C.P2.engDatumΓ hM9 B hG W wN wDec bk cons g g'))
    (hdict : Famb.VineEstS5C.P4.W2.FreeDictΓ hM9 B hG W hL γ δ η base β hβ tt ψ wN wDec bk cons g g' Mx cr)
    (hpull : ∀ x, m (clExtendIndices R ((Famb.VineEstS2.clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) =
      N.val L (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) x) :
    Famb.VineEstS5C.P4.W2.FreeDictΓ hM9 B hG W hL γ δ η base β hβ tt (spatialMul m ψ) wN wDec bk cons g g' (Mx.mul N) cr := by
  intro x
  filter_upwards [hdict x] with τ hτ
  simp only [spatialMul, hpull, CharMix.val_mul]
  calc _ = N.val L _ x * (recFac (G.sign a.toNode) (G.sign a.toNode) L γ δ tt _ *
      ψ (clExtendIndices R ((Famb.VineEstS2.clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) tt
        (clLocalClock R tt (Famb.VineEstS2.assemblyClockEquivΓ hM9 B τ))) := by ring
    _ = _ := by rw [hτ]; ring

end

section
open WaveTurbulence.VineSpaceK
open MeasureTheory DegenVine DegenVinePar VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 VineEstS5C.P4.W2 VineEstS3Par.Eng RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 VineEstS5A TTree
open scoped ENNReal
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem enginePullback_oneΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) :
    EnginePullbackΓ (γF := γF) R L base (fun _ => 1) 1 := by
  intro n hM9 B hL
  exact ⟨CharMix.one _ _, by simp, fun _ _ _ => by simp⟩

end

section
open WaveTurbulence.VineSpaceK
open MeasureTheory DegenVine DegenVinePar VineEstS5C VineEstS5C.P2 VineEstS5C.P3 VineEstS5C.P4 VineEstS5C.P4.W2 VineEstS3Par.Eng RegRed Reg.Skeleton VineParamContract VineEstS2 VineEstS3 VineEstS4 VineEstS5A TTree
open scoped ENNReal
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

end

section
open WaveTurbulence.VineSpaceK
open MeasureTheory Cut2A DegenVine VineEstS2 VineEstS3 RegRed Reg.Skeleton VineParamContract
variable {γF : ℝ}
variable {V α : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]
  [MeasurableSpace α] {d : ℕ}
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree}

/-- Algebraic bridge at the exact `EnginePullbackΓ` boundary: an affine coordinate
identity for every possible certificate assembly produces its actual mixture,
with exactly C2-A's mass. This does not supply the common-data coordinate map. -/
theorem enginePullback_of_affineΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (F : SpatialMeasure V α) (q : (GNode G.tree → Fin d → ℤ) → V)
    (hcoord : ∀ (n : ℕ) (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n) (hL : L ≠ 0),
      ∃ (A : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → Mom d →L[ℝ] V)
        (c : (Fin 4 → Mom d) → V),
      ∀ (β : Fin 4 → Fin d → ℤ)
        (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
        q (clExtendIndices R ((Famb.VineEstS2.clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1) =
          c (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) +
            ∑ v, A v (latticePoint L (x v))) :
    EnginePullbackΓ (γF := γF) R L base (fun z => F.value (q z)) F.mass := by
  intro n hM9 B hL
  obtain ⟨A, c, hc⟩ := hcoord n hM9 B hL
  refine ⟨affineCharMix _ F A c, (affineCharMix_mass _ F A c).le, ?_⟩
  intro β hβ x
  beta_reduce
  rw [hc β hβ x, affineCharMix_val]

end

section
open WaveTurbulence.VineSpaceK
open VineEstS2 VineEstS3 RegRed VineParamContract
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

theorem normalized_inverse_valΓ (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n)
    {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → Fin d → ℤ)
    (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3)
    (x : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → Fin d → ℤ) :
    ((Famb.VineEstS2.clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1 =
      fun z => clRebuildLabels R
        ((Famb.VineEstS2.chainFlowChartΓ hM9 B (β 2) (β 2 - β 3)).symm
          (fun i => jointFlip (Famb.VineEstS2.assemblyShapeΓ hM9 B) x (Famb.VineEstS2.assemblyVectorEquivΓ hM9 B i))).1 β z.1 := by
  unfold Famb.VineEstS2.clNormalizedChainEquivΓ Famb.VineEstS2.clChainCoordinateEquivΓ
  simp only [Equiv.symm_trans_apply]
  exact clLocalFromFlow_val B.isBlock R L base β hβ _

end

section
open WaveTurbulence.VineSpaceK
open MeasureTheory Cut2A DegenVine VineEstS2 VineEstS3 RegRed Reg.Skeleton VineParamContract
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

/-- Integer coefficients for each literal node of the extended normalized
local decoration. Both input and exterior coefficients are independent of β. -/
theorem normalized_node_coefficientsΓ (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n)
    (z : GNode G.tree) :
    ∃ (T : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → ℤ) (C : Fin 4 → ℤ),
    ∀ {d : ℕ} {L : ℝ} (hL : L ≠ 0) (base : Mom d) (β : Fin 4 → Fin d → ℤ)
      (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      clExtendIndices R ((Famb.VineEstS2.clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1 z =
        (∑ v, T v • x v) + ∑ j, C j • β j := by
  classical
  by_cases hs : z ∈ clLocalSupport R
  swap
  · refine ⟨0, 0, ?_⟩
    intro d L hL base β hβ x
    simp only [clExtendIndices, dite_eq_right hs, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, add_zero]
  by_cases hd : ∃ t : InternalDart G.molecule U, Mole.dartNode G t.1 = z
  · let e := ((internalBondDartEquiv G.molecule U).symm (Classical.choose hd)).1
    let T : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → ℤ := fun v =>
      Famb.VineEstS2.chainDecodeFreeΓ hM9 B e ((Famb.VineEstS2.assemblyVectorEquivΓ hM9 B).symm v) * jointFlipSign _ v
    refine ⟨T, gapBoundaryRow (Famb.VineEstS2.chainDecodeGapΓ hM9 B e), ?_⟩
    intro d L hL base β hβ x
    rw [normalized_inverse_valΓ, clExtendIndices_restrict R _ z hs]
    rw [clRebuildLabels, dite_eq_left hd]
    change ((Famb.VineEstS2.chainFlowChartΓ hM9 B (β 2) (β 2 - β 3)).symm _).1 e = _
    rw [Famb.VineEstS2.chainFlowChart_decodeΓ, gapBoundaryRow_eval]
    have hsum : (∑ i, Famb.VineEstS2.chainDecodeFreeΓ hM9 B e i •
        jointFlip (Famb.VineEstS2.assemblyShapeΓ hM9 B) x (Famb.VineEstS2.assemblyVectorEquivΓ hM9 B i)) =
        ∑ v, T v • x v := by
      rw [← (Famb.VineEstS2.assemblyVectorEquivΓ hM9 B).sum_comp]
      apply Finset.sum_congr rfl
      intro i _
      simp only [T, Equiv.symm_apply_apply, jointFlip, Equiv.coe_fn_mk, mul_smul]
    rw [hsum]
    abel
  · by_cases hb : ∃ j, clBoundaryNodes R j = z
    · refine ⟨0, fun j => if j = Classical.choose hb then 1 else 0, ?_⟩
      intro d L hL base β hβ x
      rw [normalized_inverse_valΓ, clExtendIndices_restrict R _ z hs]
      rw [clRebuildLabels, dite_eq_right hd, dite_eq_left hb]
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · refine ⟨0, 0, ?_⟩
      intro d L hL base β hβ x
      rw [normalized_inverse_valΓ, clExtendIndices_restrict R _ z hs]
      rw [clRebuildLabels, dite_eq_right hd, dite_eq_right hb]
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

end

section
open WaveTurbulence.VineSpaceK
open MeasureTheory Cut2A DegenVine VineEstS2 VineEstS3 RegRed Reg.Skeleton VineParamContract
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

/-- Every extended node momentum is affine in the normalized engine lattice,
with input maps independent of exterior momenta and clocks. -/
theorem normalized_node_affineΓ (hM9 : Famb.NormalChartSupply γF) (B : Famb.VineEstS2.CLChainAssemblyΓ γF G R n)
    (z : GNode G.tree) (L : ℝ) (base : Mom d) :
    ∃ (A : (Famb.VineEstS2.assemblyShapeΓ hM9 B).VIdx → Mom d →L[ℝ] Mom d)
      (c : (Fin 4 → Mom d) → Mom d),
    ∀ (hL : L ≠ 0) (β : Fin 4 → Fin d → ℤ)
      (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
      latticePoint L (clExtendIndices R
        ((Famb.VineEstS2.clNormalizedChainEquivΓ hL B base β hβ hM9).symm x).1 z) =
      c (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) +
        ∑ v, A v (latticePoint L (x v)) := by
  obtain ⟨T, C, hc⟩ := normalized_node_coefficientsΓ hM9 B z
  refine ⟨fun v => (T v : ℝ) • ContinuousLinearMap.id ℝ (Mom d),
    fun E => ∑ j, (C j : ℝ) • (E ((sumintBoundaryPermutation (G.sign a.toNode)).symm j) - base), ?_⟩
  intro hL β hβ x
  rw [hc hL base β hβ x]
  simp only [latticePoint_add, latticePoint_sum', latticePoint_zsmul', sumintBoundary,
    Equiv.apply_symm_apply, add_sub_cancel_left, smul_apply,
    ContinuousLinearMap.id_apply]
  exact add_comm _ _

end

section
open WaveTurbulence.VineSpaceK
open MeasureTheory Cut2A DegenVine VineEstS2 VineEstS3 RegRed Reg.Skeleton VineParamContract
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
variable {V α : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]
  [MeasurableSpace α]

/-- Actual normalized-engine realization for any affine common-data map of the
native node momenta. The C2-A density may be only integrable. No coordinate
identity or mixture-existence premise remains in this theorem. -/
theorem enginePullback_nodeMapΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (F : SpatialMeasure V α) (q0 : V) (Q : GNode G.tree → Mom d →L[ℝ] V) :
    EnginePullbackΓ (γF := γF) R L base
      (fun z => F.value (q0 + ∑ v, Q v (base + latticePoint L (z v)))) F.mass := by
  classical
  apply enginePullback_of_affineΓ
  intro n hM9 B hL
  choose A c hc using fun z => normalized_node_affineΓ hM9 B z L base
  refine ⟨fun v => ∑ z, (Q z).comp (A z v),
    fun E => q0 + ∑ z, Q z (base + c z E), ?_⟩
  intro β hβ x
  simp only [hc _ hL β hβ x, ← add_assoc, map_add, map_sum,
    sum_apply, ContinuousLinearMap.comp_apply]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  abel

end

section
open WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist RegRed Reg.Skeleton VineEstS2 VineSpaceK DegenVine Cut2A MeasureTheory
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem enginePullback_mulΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (m1 m2 : (GNode G.tree → Fin d → ℤ) → ℂ) (c1 c2 : ℝ)
    (h1 : EnginePullbackΓ (γF := γF) R L base m1 c1) (h2 : EnginePullbackΓ (γF := γF) R L base m2 c2) :
    EnginePullbackΓ (γF := γF) R L base (fun z => m1 z * m2 z) (c1 * c2) := by
  intro n hM9 B hL
  obtain ⟨N1, hN1, e1⟩ := h1 n hM9 B hL
  obtain ⟨N2, hN2, e2⟩ := h2 n hM9 B hL
  refine ⟨CharMix.mul N1 N2, ?_, ?_⟩
  · rw [CharMix.mass_mul]
    exact mul_le_mul hN1 hN2 N2.mass_nonneg (N1.mass_nonneg.trans hN1)
  · intro β hβ x
    rw [CharMix.val_mul, ← e1 β hβ x, ← e2 β hβ x]

end

section
open WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist RegRed Reg.Skeleton VineEstS2 VineSpaceK DegenVine Cut2A MeasureTheory
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem enginePullback_monoΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m : (GNode G.tree → Fin d → ℤ) → ℂ} {c c' : ℝ} (h : EnginePullbackΓ (γF := γF) R L base m c) (hc : c ≤ c') :
    EnginePullbackΓ (γF := γF) R L base m c' := by
  intro n hM9 B hL
  obtain ⟨N, hN, e⟩ := h n hM9 B hL
  exact ⟨N, hN.trans hc, e⟩

end

section
open WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist RegRed Reg.Skeleton VineEstS2 VineSpaceK DegenVine Cut2A MeasureTheory
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem enginePullback_congrΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {m m' : (GNode G.tree → Fin d → ℤ) → ℂ} {c : ℝ} (h : EnginePullbackΓ (γF := γF) R L base m c) (he : m = m') :
    EnginePullbackΓ (γF := γF) R L base m' c := he ▸ h

end

section
open WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist RegRed Reg.Skeleton VineEstS2 VineSpaceK DegenVine Cut2A MeasureTheory
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem enginePullback_finsetProdΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → (GNode G.tree → Fin d → ℤ) → ℂ) (c : ι → ℝ)
    (h : ∀ i ∈ s, EnginePullbackΓ (γF := γF) R L base (f i) (c i)) :
    EnginePullbackΓ (γF := γF) R L base (fun z => ∏ i ∈ s, f i z) (∏ i ∈ s, c i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact enginePullback_oneΓ R L base
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact enginePullback_mulΓ R L base _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end

section
open WaveTurbulence.VineSpaceB
open WaveTurbulence TTree Twist RegRed Reg.Skeleton VineEstS2 VineSpaceK DegenVine Cut2A MeasureTheory
variable {γF : ℝ}
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- A spatial measure of one node momentum is realized with its mass. -/
theorem enginePullback_nodeValueΓ (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    {α : Type} [MeasurableSpace α] (M : SpatialMeasure (Mom d) α) (n0 : GNode G.tree) :
    EnginePullbackΓ (γF := γF) R L base (fun z => M.value (cosetDecoration G L base z n0)) M.mass := by
  classical
  refine enginePullback_congrΓ R L base (enginePullback_nodeMapΓ R L base M 0
    (fun v => if v = n0 then ContinuousLinearMap.id ℝ (Mom d) else 0)) ?_
  funext z
  congr 1
  rw [zero_add, Finset.sum_eq_single n0 (fun v _ hv => by simp [hv]) (fun h => absurd (Finset.mem_univ n0) h)]
  simp [cosetDecoration]

end

end WaveTurbulence.GammaLow.Flower
