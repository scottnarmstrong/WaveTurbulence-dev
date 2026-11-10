/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WRegion3
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.FwNode
public import WaveTurbulence.Foundations.Vine.Align.Export
public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationGeometry

/-! # STAGE1W-VINE (weighted VINE-ALIGN, part 1): the weighted slot kernel with explicit root weight layers

* `slotKerQ`: the frontier-weighted native kernel of a slot (`coupleLeavesTopR` / `treeLeavesTop` at the native object and
  its native profiles), with per-root weights `g (tree of the root)` and an explicit vector of root weight layers.
* `slotFW_eq_kerQ`: the frontier-weighted slot family `slotFW` is `slotKerQ` at the weight layers `wLay`: `p + 1` (no
  factor) at a skeleton root (a garden root, finding F-ROOT), the core layer of the parent branch otherwise.
* `ordinary_couple_kerQ`, `ordinary_tree_kerQ`: for every vector of weight layers, the kernel of an ordinary slot is
  unchanged by an LF construction (native objects `native_couple_eq`/`native_tree_eq`, native profiles as in main's
  `ordinary_couple_kernel`, tree indices `ordinary_couple_root_index`/`branches_index`).

Adapted from main's `Vine/Align/NativeKernels.lean` (see `COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed Finset WaveTurbulence.Represents Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.LFTwist WaveTurbulence.Links
  WaveTurbulence.VineAlign

/-! ## Generic congruences -/

/-- At a garden root the weight layer `p + 1` and the root's own layer both give no factor. -/
theorem topPsi_self_succ {d : ℕ} (p : ℕ) (g : Mom d → ℂ) (q : ℕ) (x : Mom d) :
    topPsi p g q q x = topPsi p g q (p + 1) x := by
  unfold topPsi
  rw [if_neg (by omega), if_neg (by omega)]

/-! ## The weighted slot kernel with explicit root weight layers -/

section Ker
variable {w d : ℕ} {S : Garden w}

/-- The weight layer read from a clock source: `p + 1` (no factor) at a root clock, the core layer otherwise. -/
def wLay (p : ℕ) (layer0 : GBranch S.tree → ℕ) : ClkSrc S → ℕ
  | .inl _ => p + 1
  | .inr b => layer0 b

variable (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

theorem argSrc_couple (q : SourcePair S) (j : Fin 2) :
    argSrc hS (.inl q) j = clkOfNode S (if j = 0 then (q.firstLeaf hS).toNode else (q.secondLeaf hS).toNode) := by
  fin_cases j <;> simp [argSrc]

/-- The root factor of a couple slot at its weight layer `cplQ` is the one at `wLay` of its clock source. -/
theorem cplQ_root_factor (p : ℕ) (G : Mom d → ℂ) (q : SourcePair S) (j : Fin 2) (x : Mom d) :
    topPsi p G ((nativeCoupleLayered D hS layer hLayer q).layer
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree j))
        (Stage1WNoVine.cplQ D hS layer hLayer p q j) x =
      topPsi p G ((nativeCoupleLayered D hS layer hLayer q).layer
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree j))
        (wLay p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inl q) j)) x := by
  set ν : GNode S.tree := if j = 0 then (q.firstLeaf hS).toNode else (q.secondLeaf hS).toNode with hν
  have hroot := couple_root_node D hS q j
  rw [argSrc_couple]
  unfold Stage1WNoVine.cplQ Stage1WNoVine.embQ
  have hpath : (((nativeCoupleForest D hS q).root j).1).2 ++ [] =
      (inflatedPosition S D.tree ν).2 := congrArg Prod.snd hroot
  rw [List.append_nil] at hpath
  by_cases hn : ν.1.2 = []
  · have hr : (((nativeCoupleForest D hS q).root j).1).2 = [] := by
      rw [hpath]
      have h1 : ν = GNode.root S.tree ν.1.1 := Subtype.ext (Prod.ext rfl hn)
      rw [h1, inflatedPosition_root]
    rw [if_pos hr, ← hν, VineB.SpliceShape.clkOfNode_root ν hn]
    exact topPsi_self_succ p G _ x
  · have hr : (((nativeCoupleForest D hS q).root j).1).2 ≠ [] := by
      rw [hpath]
      exact inflatedPosition_nonroot S D.tree ν hn
    rw [if_neg hr, ← hν]
    have hpl := parentLayer_inflated D hS layer hLayer p ν
      ((nativeCoupleForest D hS q).nodeEmbedding
        (GNode.root (nativeCoupleLayered D hS layer hLayer q).garden.tree j)) hroot
    rw [hpl, VineB.clkOfNode_nonroot ν hn]
    rfl

/-- The root factor of a tree slot at its weight layer `treeQ` is the one at `wLay` of its clock source. -/
theorem treeQ_root_factor (p : ℕ) (G : Mom d → ℂ) (b : GBranch S.tree) (x : Mom d) :
    topPsi p G ((nativeChainLayered D hS layer hLayer b).layer
        (GNode.root (nativeChainLayered D hS layer hLayer b).garden.tree 0))
        (Stage1WNoVine.treeQ D hS layer hLayer p b) x =
      topPsi p G ((nativeChainLayered D hS layer hLayer b).layer
        (GNode.root (nativeChainLayered D hS layer hLayer b).garden.tree 0))
        (wLay p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS (.inr b) 0)) x := by
  have hroot := tree_root_node D hS b
  have ha : argSrc hS (.inr b) 0 = clkOfNode S b.toNode := by simp [argSrc]
  rw [ha]
  unfold Stage1WNoVine.treeQ Stage1WNoVine.embQ
  by_cases hn : b.toNode.1.2 = []
  · have hr : (inflatedPosition S D.tree b.toNode).2 = [] := by
      have h1 : b.toNode = GNode.root S.tree b.toNode.1.1 := Subtype.ext (Prod.ext rfl hn)
      rw [h1, inflatedPosition_root]
    rw [if_pos hr, VineB.SpliceShape.clkOfNode_root b.toNode hn]
    exact topPsi_self_succ p G _ x
  · have hr : (inflatedPosition S D.tree b.toNode).2 ≠ [] := inflatedPosition_nonroot S D.tree b.toNode hn
    rw [if_neg hr]
    have hpl := parentLayer_inflated D hS layer hLayer p b.toNode
      (chainContextNode D hS b (GNode.root (nativeChainLayered D hS layer hLayer b).garden.tree 0)) hroot
    rw [hpl, VineB.clkOfNode_nonroot b.toNode hn]
    rfl

end Ker

/-! ## One LF construction leaves the kernel of an ordinary slot unchanged -/

section LF
variable {w p d : ℕ} {kind ε : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG}
  (h : LFConstruction s ε)
  (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
  (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
  (layer' : GNode (h.data.forest (s.chosen_plain ε)) → ℕ)
  (hLayer' : IsLayering (h.data.garden (s.chosen_plain ε)) layer')
  (hspec' : layeredReconstruction h.data (s.chosen_plain ε) layer' hLayer' = h.output)
  (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ) (pw : ℕ) (g : Fin w → Mom d → ℂ)

include hspec hspec'

end LF

end WaveTurbulence.Flower.Stage1WVine
