/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1W.Defs
public import WaveTurbulence.Foundations.Flower.Stage1W.Inputs
public import WaveTurbulence.Foundations.VineEst.VineSpaceB.BondStatements
public import WaveTurbulence.Foundations.Vine.C.VCApi
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModClass
public import WaveTurbulence.Foundations.Vine.DegenVine.CharMix
public import WaveTurbulence.Foundations.SumintPar.SourceKernelInterpolated
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GateH
public import WaveTurbulence.Foundations.Fourier.CutoffFourierDecay
public import WaveTurbulence.Foundations.Spine.LeafwiseLayerInputs
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P1.Mix
public import WaveTurbulence.Frozen.Defs.KernelK
public import WaveTurbulence.Frozen.Defs.Chi0
public import WaveTurbulence.Frozen.Defs.ResFactor
public import WaveTurbulence.Frozen.Defs.LayeredGardenParentLayer
public import WaveTurbulence.Foundations.VineEst.RowSel.RowData

/-! # V5W-0: the pinned kernel form of the weighted vine estimate (S-V5W SCOPE §1)

Ported by source from the S-V5W probe `scope/S-V5W/probe/V5WProbe.lean` (sha256 `efdab782…f05f6`, see
`COPIED-SHA256SUMS`), §1 and §4, re-homed from `WaveTurbulence.Flower.Probe.V5W` to `WaveTurbulence.Flower.V5W`.
The weight vocabulary (`topPsi`, `rowTopWeight`, `coupleLeavesTop`, `treeLeavesTop`, `GPresented`, …) is imported from
STAGE1W-GLUE's G1 module (`Flower.Stage1W.Defs`), as the scope requires; it is not re-defined.

* `topFilterWeight S`, `topFilterMass`: the region-top stem filter (supplement Lemma 9.3).
* `clLocalStarProductFW`: coherent rows (incoherency `0`) carry main's `KQstar`/`KTstar`; incoherent rows carry their own
  top weight (`coupleLeavesTop`/`treeLeavesTop` at the layer profiles).
* `regionWeightFW`: the masked R135 bond product over the darts of the region whose row is coherent, times the top filter.
* `twistedRecenteredFW`: **the pinned class kernel**, the recentered sum over the class of each member's own weighted
  kernel; `unitKernelFW`, `unitRecenteredFW`: the per-state unit kernels (VINE-C form).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB WaveTurbulence.VineC WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W
open scoped ENNReal FourierTransform
open Set
open VineEstS5C.P4.Final LGSpine Cut2A

/-! ## §1 The region-top stem filter (supplement Lemma 9.3) -/

/-- The low-pass resonance filter at one branch (one factor of `stemFilter`, T/supplement (8.1)), as a
`VineSpaceK.nodeWeight` of `![k_v, k_{v0}, k_{v1}, k_{v2}]`: `χ₀(|Ω_v|/S)` (`S = none`: no filter).
`omegaNode G k v = resFactor (k v0) (k v1) (k v2) (k v)`. -/
def topFilterWeight {d : ℕ} (S : Option ℝ) : (Fin 4 → Mom d) → ℂ :=
  fun q => ((S.elim 1 fun s => WaveTurbulence.chi0 (|resFactor (q 1) (q 2) (q 3) (q 0)| / s) : ℝ) : ℂ)

/-- Total variation of the one-dimensional Fourier representation of `χ₀(|·|) = Fourier.chi0` (Lemma 9.3's mass). -/
def topFilterMass : ℝ := ∫ v : ℝ, ‖𝓕 Fourier.chi0Complex v‖

/-! ## §4 (B) The pinned kernel form -/

/- `coupleIncoh`, `treeIncoh`, `coupleRootParents`, `treeRootParent` are now on main (416902c8, V5W-B:
`VineEst/RowSel/RowData.lean`, the same text in this namespace), imported above. -/

/-- **The selected regional factor** (the only change against `RegRed.clLocalStarProduct`): coherent rows
(incoherency `0`) carry main's `KQstar`/`KTstar` (their frontier crossing is the bond factor, supplement Lemma 5.1);
incoherent rows carry their own top weight, `coupleLeavesTop`/`treeLeavesTop` at the layer profiles (Lemma 4.1). -/
def clLocalStarProductFW {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (p : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain)
    (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (κ : GNode G.tree → (Fin d → ℤ))
    (t : Fin 3 → ℝ) (τ : CLInternalTime R) : ℂ :=
  let u := clLocalClock R t τ
  (∏ pr ∈ clRegionalPairs hG U,
    if coupleIncoh D hG layer hLayer pr = 0 then
      KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer pr)
        (parentClock (t 0) u (pr.firstLeaf hG).toNode) (parentClock (t 0) u (pr.secondLeaf hG).toNode)
        (cosetDecoration G L base κ (pr.firstLeaf hG).toNode)
    else
      coupleLeavesTop L γ δ p g (coupleRootParents p D hG layer hLayer pr 0) (coupleRootParents p D hG layer hLayer pr 1)
        (nativeCoupleLayered D hG layer hLayer pr) (layerProfiles (nativeCoupleLayered D hG layer hLayer pr) F)
        (parentClock (t 0) u (pr.firstLeaf hG).toNode) (parentClock (t 0) u (pr.secondLeaf hG).toNode)
        (cosetDecoration G L base κ (pr.firstLeaf hG).toNode)) *
  (∏ v ∈ clInteriorBranches R,
    if treeIncoh D hG layer hLayer v = 0 then
      KTstar L γ δ F (nativeChainLayered D hG layer hLayer v)
        (parentClock (t 0) u v.toNode) (u v) (cosetDecoration G L base κ v.toNode)
    else
      treeLeavesTop L γ δ p g (treeRootParent p D hG layer hLayer v) (nativeChainLayered D hG layer hLayer v)
        (layerProfiles (nativeChainLayered D hG layer hLayer v) F)
        (parentClock (t 0) u v.toNode) (u v) (cosetDecoration G L base κ v.toNode))

/-- The local summand with the selected factor (copy of `RegRed.clLocalSummand`). -/
def clLocalSummandFW {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (p : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain)
    (R : CLRegionData G U a b) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (boundary : Fin 4 → Mom d)
    (t : Fin 3 → ℝ) (κ : CLLocalDecoration R L base boundary) (τ : CLInternalTime R) : ℂ :=
  (clRegionalEpsilon G U (clExtendIndices R κ.1) : ℂ) *
    (clLocalTimeDomain R (fun v => layer (D.coreBranch hG v).toNode) t).indicator
      (fun τ => clRegionalPhase G U L γ δ (cosetDecoration G L base (clExtendIndices R κ.1))
          (clLocalClock R t τ) *
        clLocalStarProductFW p g D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t τ) τ

/-- The local kernel with selected rows, a spatial multiplier `m` and the lower-joint time weight `W`
(copy of `VineC.clLocalKernelW` with `clLocalSummandFW` and `m`). -/
def clLocalKernelFW {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (p : ℕ) (g : Mom d → ℂ) (D : ReconstructionData G) (hG : G.IsPlain) (R : CLRegionData G U a b)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
    (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)
    (m : (GNode G.tree → Fin d → ℤ) → ℂ) (W : ℝ → ℂ)
    (tUpper tPositive tNegative : ℝ) (e f g' h : Mom d) : ℂ :=
  (coupling d L γ δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R *
    ∑' κ : CLLocalDecoration R L base ![e, f, g', h],
      ∫ τ : CLInternalTime R, m (clExtendIndices R κ.1) *
        (clLocalSummandFW p g D hG R L γ δ F layer hLayer base ![e, f, g', h] ![tUpper, tPositive, tNegative] κ τ *
          W (clLocalClock R ![tUpper, tPositive, tNegative] τ b))

open Classical in
/-- The incoherency index of the row carried by a skeleton node (a branch: its regular tree; a leaf: the regular couple
of its source pair). -/
def nodeRowIncoh {w : ℕ} {G : Garden w} (D : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (x : GNode G.tree) : ℕ :=
  if h : ∃ c : GBranch G.tree, c.toNode = x then treeIncoh D hG layer hLayer h.choose
  else if h' : ∃ pr : SourcePair G, (pr.firstLeaf hG).toNode = x ∨ (pr.secondLeaf hG).toNode = x then
    coupleIncoh D hG layer hLayer h'.choose
  else 0

/-- The core layer of a skeleton branch of a state (= `VineSpaceB.memberCoreLayer` on class members). -/
def stateCoreLayer {w : ℕ} {ι : Type*} (X : FamilyReconstruction w ι) (v : GBranch X.skeleton.tree) : ℕ :=
  layerAt X.layered (X.data.corePosition v)

/-- **The region multiplier of a state on a block `(U, a)`**: the R135 bond product restricted to darts whose row is
coherent (masked `regionBondWeight` at `topPsi p g`), times the top filter at the region top. -/
def regionWeightFW {w d : ℕ} {ι : Type*} (p : ℕ) (g : Mom d → ℂ) (S : Option ℝ) (L : ℝ) (base : Mom d)
    (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree)) (a : GBranch X.skeleton.tree)
    (x : GNode X.skeleton.tree → Fin d → ℤ) : ℂ :=
  (∏ y ∈ Finset.univ.filter (X.skeleton.molecule.InGroup U),
    if nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y) = 0 then
      topPsi p g (stateCoreLayer X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)))
        (stateCoreLayer X (X.skeleton.molecule.atom y))
        (cosetDecoration X.skeleton L base x (Mole.dartNode X.skeleton y))
    else 1) *
  nodeWeight (topFilterWeight S) L base a x

/-- The weighted kernel of a class member `(state, chain region)` (cf. `VineC.twistedLocalKernelW`). -/
def twistedLocalKernelFW {w d : ℕ} {κ : Type*} (p : ℕ) (g : Mom d → ℂ) (S : Option ℝ)
    (Bs : FamilyReconstruction w κ) (c : ChainAt Bs.skeleton Bs.family)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d) : ℂ :=
  clLocalKernelFW p g Bs.data Bs.plain (clRegionData Bs.skeleton c.block c.cl) L γ δ F (stateLayer Bs)
    (stateLayer_isLayering Bs) base (regionWeightFW p g S L base Bs c.U c.a) W t0 t1 t2 e f g' h

/-- **THE PINNED CLASS KERNEL** `K̃^{U}_{FW}`: the recentered sum over the class of each member's OWN weighted kernel
(cf. `VineC.twistedRecenteredW`; `W = modW λ` is V5's modulation). -/
def twistedRecenteredFW {w d : ℕ} {κ : Type*} (p : ℕ) (g : Mom d → ℂ) (S : Option ℝ) (G : Garden w)
    (a : GBranch G.tree) (Z : Finset (Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family))
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d) : ℂ :=
  recPhase (G.sign a.toNode) L γ δ t0 e f g' h *
    ∑ x ∈ Z, twistedLocalKernelFW p g S x.1 x.2 L γ δ F base W t0 t1 t2 e f g' h

/-- The weighted unit kernel of a state (cf. `VineC.unitKernelW`). -/
def unitKernelFW {w d : ℕ} {ι : Type*} {Q : ι → Prop} (p : ℕ) (g : Mom d → ℂ) (S : Option ℝ)
    (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d) : ℂ :=
  clLocalKernelFW p g X.data X.plain (clRegionData X.skeleton u.blk.block u.cl) L γ δ F (stateLayer X)
    (stateLayer_isLayering X) base (regionWeightFW p g S L base X u.blk.U u.blk.a) W t0 t1 t2 e f g' h

/-- The recentered weighted unit kernel (cf. `VineC.unitRecenteredW`). -/
def unitRecenteredFW {w d : ℕ} {ι : Type*} {Q : ι → Prop} (p : ℕ) (g : Mom d → ℂ) (S : Option ℝ)
    (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d) : ℂ :=
  recPhase (X.skeleton.sign u.blk.a.toNode) L γ δ t0 e f g' h *
    unitKernelFW p g S X u L γ δ F base W t0 t1 t2 e f g' h

/-! ## Sanity (S-V5W probe §8, proved there; re-proved here) -/

end WaveTurbulence.Flower.V5W
