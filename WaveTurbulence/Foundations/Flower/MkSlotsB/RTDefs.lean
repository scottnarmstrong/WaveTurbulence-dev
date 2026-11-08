/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.SlotObl
public import WaveTurbulence.Foundations.Flower.MkSlotsO.RootTraceHyp
public import WaveTurbulence.Foundations.Flower.MkSlots.CapConv

/-! # B3s-HELPER3 (B5(ii), ruling R188): the off-stem root-trace slots and their geometric data

A **root-trace slot** (F-H3-4 = case (e) of HELPER8's S2): a `dChild i` pattern on the tree of a CORE capped flower
parent `F = core β` (the cap couple at the flower is trivial); child `i` of `F` is a branch `r`, not a core node,
pinned at `s`; the slot is the slot of `r`. By the skeleton decomposition it is either
* the chain slot `.inr γ'` of the skeleton child `γ'` of `β` (nontrivial chain, `r` its top), or
* the leaf-pair slot `.inl q'` of the skeleton leaf child of `β` (`r` a root of the native couple).

The B5(ii) assembly consumes the slot through the geometric data `RTChain` / `RTCouple` (pins = the roots at `s`,
layers, ambient, off-stem consequences for the general per-slot factor, node weight and selections, clocks, leaf
control, frontier count). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
  WaveTurbulence.VineAlign WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtDefs
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.Stage1W

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-- **A root-trace slot**: the slot of the pinned `dChild i` child `r` (a non-core branch) of a CORE capped flower
parent `F = core β`. -/
def RootTraceSlot (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat)
    (sl : ReplacementSlot a.prime.skeleton) : Prop :=
  ∃ (β : GBranch a.prime.skeleton.tree) (i : Fin 3) (r : GBranch (a.prime.data.forest a.prime.prime.1)),
    IsCapFlowerParent (MkSlots.recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β) ∧
    pat β.1.1 = FixPat.dChild i ∧ r.toNode = (a.prime.data.coreBranch a.prime.prime.1 β).child i ∧
    (∀ β' : GBranch a.prime.skeleton.tree, (a.prime.data.coreBranch a.prime.prime.1 β').toNode ≠ r.toNode) ∧
    MkSlots.slotOf a.prime.data a.prime.prime.1 r.toNode = sl

/-- The frontier nodes of a native object (for the star weights of the frontier cutoffs). -/
def frontNat (a : PrescribedPrimeGarden w) {T : Fin 1 → TTree} (e : GNode T → GNode (MkSlots.recLG a).garden.tree) (p : ℕ) :
    Finset (GNode T) :=
  Finset.univ.filter fun z => (e z).1.2 ≠ [] ∧ (MkSlots.recLG a).layer (e z) < p ∧
    (MkSlots.recLG a).parentLayer p (e z) = p

/-- The frontier nodes of a native couple. -/
def frontNat2 (a : PrescribedPrimeGarden w) {T : Fin 2 → TTree} (e : GNode T → GNode (MkSlots.recLG a).garden.tree) (p : ℕ) :
    Finset (GNode T) :=
  Finset.univ.filter fun z => (e z).1.2 ≠ [] ∧ (MkSlots.recLG a).layer (e z) < p ∧
    (MkSlots.recLG a).parentLayer p (e z) = p

/-- **The geometric data of a root-trace CHAIN slot `.inr γ'`** (tree variant): `X = D.tree γ'` nontrivial
(`2 ≤ |lonePath|`), only the root pinned (at `s`), layers `≤ p` with the root in layer `p` and the lone node in the
layer of the core of `γ'`, canonical ambient; off the capped stems (`genΘs ≡ 1`, no selected native vertex, node
weight = frontier weight); upper clock pinned at `s` in layer `p`, lower clock `γ'` free, `γ'` not a skeleton root;
never `SelAdj` (the tree is a `dChild` tree); a protected native node (the root); leafwise control. -/
structure RTChain (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (p : ℕ)
    (γ' : GBranch a.prime.skeleton.tree) : Prop where
  two_le : 2 ≤ (a.prime.data.tree γ').lonePath.length
  wf : (a.prime.data.tree γ').wf = true
  pins : ∀ q : GBranch (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) γ').garden.tree,
    MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s) (.inr γ') q =
      MkSlotsO.rootPins (fun _ => True) s q
  layer_le : ∀ z, (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) γ').layer z ≤ p
  layer_root : (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) γ').layer (GNode.root _ 0) = p
  layer_lone : ∀ z : GNode (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) γ').garden.tree, z.1.2 = (a.prime.data.tree γ').lonePath →
    (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) γ').layer z =
      sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 γ').toNode
  amb : ProtAmbient p (a.prime.data.tree γ')
    (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) γ')
  genΘs_one : ∀ {d : ℕ} (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (k : Mom d)
    (κ : NativeRelativeDecoration a.prime.data a.prime.prime.1 d (.inr γ')),
    MkSlotsI.genΘs a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs (.inr γ')
      k κ = 1
  selNative_empty : ∀ kSel : Fin w → Option ℕ,
    MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (.inr γ') = ∅
  chainW_eq : ∀ {d : ℕ} (L γ δ s' : ℝ) (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (z : GNode (decodedTree (a.prime.data.tree γ') (nodeSign a.prime.skeleton.sig γ'.1)).tree) (x : Mom d),
    MkSlots.chainW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) L γ δ p s' J Rf dag
        (chainContextNode a.prime.data a.prime.prime.1 γ' z) x =
      fwNode (MkSlots.recLG a) p (fun j => frontierG (Rf j)) (chainContextNode a.prime.data a.prime.prime.1 γ' z) x
  clk0 : MkSlotsI.clkPin (fun _ => t) (MkSlots.fixCore a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s))
    (argSrc a.prime.prime.1 (.inr γ') 0) = some s
  clkLayer0 : clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
    (argSrc a.prime.prime.1 (.inr γ') 0) = p
  free : MkSlots.fixCore a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s) γ' = none
  nonroot : γ'.1.2 ≠ []
  notSelAdj : ∀ kSel : Fin w → Option ℕ, (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    ¬ MkSlotsI.SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (.inr γ')
  prot : ∀ kSel : Fin w → Option ℕ, MkSlotsI.HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) (protI (MkSlots.recLG a) J pat t s kSel) (.inr γ')
  leafwise : ∀ {d : ℕ} (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ) (roots : Fin w → (Fin d → ℤ)) (b : ℝ), 0 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal b) →
    LeafwiseControlled (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) γ')
      (MkSlots.capProfiles (nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) γ')
        (fun z => MkSlots.anchProfiles J (MkSlots.recLG a) h L roots (chainContextNode a.prime.data a.prime.prime.1 γ' z).1))
      (nativeChainB a.prime.data a.prime.prime.1 (fun _ => b.toNNReal) γ')
  front_card : (frontNat a (chainContextNode a.prime.data a.prime.prime.1 γ') p).card ≤
    slotNr a.prime.data a.prime.prime.1 (.inr γ')

/-- **The geometric data of a root-trace COUPLE slot `.inl q'`** (couple variant), with the set `Rt ≠ ∅` of trees
whose root is pinned (at `s`): not a cap pair; only the roots in `Rt` pinned; layers `≤ p`, the pinned roots
branching in layer `p`, the roots below their clock windows; canonical signed ambient with the clock windows as root parent layers (F-RT-3); off the capped stems; never
`SelAdj` when both roots are pinned; a protected native node; leafwise control; the box inside the gate's box `timeBox q q' ∩ {s ≤ ts j, j ∈ Rt}`. -/
structure RTCouple (a : PrescribedPrimeGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (p : ℕ)
    (q' : SourcePair a.prime.skeleton) (Rt : Fin 2 → Prop) : Prop where
  rt : ∃ j, Rt j
  notCap : ¬ MkSlots.IsCapPair a.prime.skeleton a.prime.prime.1 J q'
  wf : (a.prime.data.couple q').wf = true
  pins : ∀ q : GBranch (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q').garden.tree,
    MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s) (.inl q') q =
      MkSlotsO.rootPins Rt s q
  layer_le : ∀ z, (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q').layer z ≤ p
  root_pinned : ∀ j, Rt j → ([] : Path) ∈ ((nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q').garden.tree j).branching ∧
    (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q').layer
      (GNode.root _ j) = p
  root_le : ∀ j, (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) q').layer (GNode.root _ j) ≤
    clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
      (argSrc a.prime.prime.1 (.inl q') j)
  amb : MkSlotsO.CplAmbient p
    (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
      (argSrc a.prime.prime.1 (.inl q') 0))
    (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
      (argSrc a.prime.prime.1 (.inl q') 1))
    (a.prime.data.couple q')
    (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q')
  genΘs_one : ∀ {d : ℕ} (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (k : Mom d)
    (κ : NativeRelativeDecoration a.prime.data a.prime.prime.1 d (.inl q')),
    MkSlotsI.genΘs a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs (.inl q')
      k κ = 1
  selNative_empty : ∀ kSel : Fin w → Option ℕ,
    MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (.inl q') = ∅
  chainW_eq : ∀ {d : ℕ} (L γ δ s' : ℝ) (Rf : Fin w → Option ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (z : GNode (nativeCoupleGarden a.prime.data a.prime.prime.1 q').tree) (x : Mom d),
    MkSlots.chainW a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) L γ δ p s' J Rf dag
        ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z) x =
      fwNode (MkSlots.recLG a) p (fun j => frontierG (Rf j))
        ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z) x
  notSelAdj : Rt 0 ∧ Rt 1 → ∀ kSel : Fin w → Option ℕ,
    ¬ MkSlotsI.SelAdj a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel (.inl q')
  prot : ∀ kSel : Fin w → Option ℕ, MkSlotsI.HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) (protI (MkSlots.recLG a) J pat t s kSel) (.inl q')
  leafwise : ∀ {d : ℕ} (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ) (roots : Fin w → (Fin d → ℤ)) (b : ℝ), 0 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal b) →
    LeafwiseControlled (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q')
      (MkSlots.capProfiles (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a) q')
        (fun z => MkSlots.anchProfiles J (MkSlots.recLG a) h L roots
          ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding z).1))
      (nativeCoupleB a.prime.data a.prime.prime.1 (fun _ => b.toNNReal) q')
  front_card : (frontNat2 a ((nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding) p).card ≤
    slotNr a.prime.data a.prime.prime.1 (.inl q')
  box : MkSlotsI.genBoxAt p a J pat t s (.inl q') ⊆
    timeBox (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1 (.inl q') 0))
      (clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1 (.inl q') 1)) ∩ {ts | ∀ j, Rt j → s ≤ ts j}

end WaveTurbulence.Flower.MkSlotsB
