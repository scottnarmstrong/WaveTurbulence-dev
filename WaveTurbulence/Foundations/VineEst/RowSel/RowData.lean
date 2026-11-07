/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.NativeChainLayering
public import WaveTurbulence.Frozen.Defs.LayeredGardenParentLayer
public import WaveTurbulence.Frozen.Defs.LayeredGardenIncoherency

/-! # V5W-B (ruling F2): the row data the selector reads, copied by source

The four definitions `coupleIncoh`, `treeIncoh`, `coupleRootParents`, `treeRootParent` are copied verbatim (text and
namespace `WaveTurbulence.Flower.V5W` unchanged) from V5W-0's `Flower/V5W/Defs.lean` (sha256
`efe85fcbafa6cb7c5258fd976956c89435ccbb437de13461de308ff886d9f1c2`, lines 68–91): the incoherency index of the native
couple of a source pair and of the native tree of a branch, and the parent layers of their roots in the reconstructed
garden.  Only the module header differs: the `open` list is reduced to the namespaces that exist below the V5 tower
(the four bodies use none of the dropped ones).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree

/-- Incoherency index of the native couple of a source pair (as `VineEstS3.rowCoupleG`). -/
def coupleIncoh {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (pr : SourcePair S) : ℕ :=
  (nativeCoupleLayered D hS layer hLayer pr).incoherency (D.couple pr).links

/-- Incoherency index of the native regular tree of a branch (as `VineEstS3.rowTreeG`). -/
def treeIncoh {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (v : GBranch S.tree) : ℕ :=
  (nativeChainLayered D hS layer hLayer v).incoherency
    ((D.tree v).treeLinks ((nativeChainLayered D hS layer hLayer v).garden.sig 0))

/-- The parent layers of the two roots of the native couple of a source pair, read in the reconstructed garden
(the `qr` of `rowTopWeight`). -/
def coupleRootParents {w : ℕ} {S : Garden w} (p : ℕ) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (pr : SourcePair S) : Fin 2 → ℕ :=
  fun i => (layeredReconstruction D hS layer hLayer).parentLayer p
    ((nativeCoupleForest D hS pr).nodeEmbedding (GNode.root (nativeCoupleLayered D hS layer hLayer pr).garden.tree i))

/-- The parent layer of the root of the native regular tree of a branch, read in the reconstructed garden. -/
def treeRootParent {w : ℕ} {S : Garden w} (p : ℕ) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (v : GBranch S.tree) : ℕ :=
  (layeredReconstruction D hS layer hLayer).parentLayer p
    (chainContextNode D hS v (GNode.root (nativeChainLayered D hS layer hLayer v).garden.tree 0))


end WaveTurbulence.Flower.V5W
