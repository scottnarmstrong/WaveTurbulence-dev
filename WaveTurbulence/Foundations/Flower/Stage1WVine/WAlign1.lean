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

/-- Only the profiles of actual input leaves affect a weighted leafwise kernel. -/
theorem kernelLeavesW_congr_inputs {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H H' : LeafProfiles w d) (hH : ∀ l ∈ inputLeaves LG.garden, H l.1 = H' l.1)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    kernelLeavesW L γ δ LG H up s k roots nfl m = kernelLeavesW L γ δ LG H' up s k roots nfl m := by
  unfold kernelLeavesW
  congr 1
  refine tsum_congr fun z => ?_
  congr 2
  exact Finset.prod_congr rfl fun l hl => by rw [hH l hl]

/-- Pointwise equal multipliers give equal weighted leafwise kernels. -/
theorem kernelLeavesW_congr_m {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : Mom d) (roots : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m m' : (GNode LG.garden.tree → Mom d) → ℂ) (hm : ∀ x, m x = m' x) :
    kernelLeavesW L γ δ LG H up s k roots nfl m = kernelLeavesW L γ δ LG H up s k roots nfl m' := by
  rw [show m = m' from funext hm]

/-- A row weight only reads its root weight layers through the root factors. -/
theorem rowTopWeightR_congr_q {w d : ℕ} (p : ℕ) (G : Fin w → Mom d → ℂ) (LG : LayeredGarden w) (qr qr' : Fin w → ℕ)
    (h : ∀ j x, topPsi p (G j) (LG.layer (GNode.root LG.garden.tree j)) (qr j) x =
      topPsi p (G j) (LG.layer (GNode.root LG.garden.tree j)) (qr' j) x)
    (k : GNode LG.garden.tree → Mom d) :
    rowTopWeightR p G LG qr k = rowTopWeightR p G LG qr' k := by
  unfold rowTopWeightR
  refine Finset.prod_congr rfl fun a _ => ?_
  unfold rowParentLayer
  by_cases ha : a.1.2 = []
  · rw [if_pos ha, if_pos ha]
    obtain ⟨⟨j, r⟩, hr⟩ := a
    simp only at ha
    subst ha
    exact h j _
  · rw [if_neg ha, if_neg ha]

/-- At a garden root the weight layer `p + 1` and the root's own layer both give no factor. -/
theorem topPsi_self_succ {d : ℕ} (p : ℕ) (g : Mom d → ℂ) (q : ℕ) (x : Mom d) :
    topPsi p g q q x = topPsi p g q (p + 1) x := by
  unfold topPsi
  rw [if_neg (by omega), if_neg (by omega)]

/-! ## The weighted slot kernel with explicit root weight layers -/

section Ker
variable {w d : ℕ} {S : Garden w}

/-- The frontier-weighted native kernel of a slot with root weight layers `qv`. -/
def slotKerQ (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (L γ δ : ℝ) (H : LeafProfiles w d) (p : ℕ)
    (g : Fin w → Mom d → ℂ) : ReplacementSlot S → (Fin 2 → ℕ) → (Fin 2 → ℝ) → Mom d → ℂ
  | .inl q => fun qv ts k => coupleLeavesTopR L γ δ p (fun j => g (coupleRoot D hS q j).1) (qv 0) (qv 1)
      (nativeCoupleLayered D hS layer hLayer q) (nativeCoupleProfiles D hS H q) (ts 0) (ts 1) k
  | .inr b => fun qv ts k => treeLeavesTop L γ δ p (g b.1.1) (qv 0)
      (nativeChainLayered D hS layer hLayer b) (nativeChainProfiles D hS H b) (ts 0) (ts 1) k

/-- The weight layer read from a clock source: `p + 1` (no factor) at a root clock, the core layer otherwise. -/
def wLay (p : ℕ) (layer0 : GBranch S.tree → ℕ) : ClkSrc S → ℕ
  | .inl _ => p + 1
  | .inr b => layer0 b

theorem fwNodeV_eq_fwNode (LG : LayeredGarden w) (p : ℕ) (g : Fin w → Mom d → ℂ) :
    fwNodeV LG p g = Stage1WNoVine.fwNode LG p g := rfl

variable (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer)

theorem argSrc_couple (q : SourcePair S) (j : Fin 2) :
    argSrc hS (.inl q) j = clkOfNode S (if j = 0 then (q.firstLeaf hS).toNode else (q.secondLeaf hS).toNode) := by
  fin_cases j <;> simp [argSrc]

theorem couple_root_emb (q : SourcePair S) (j : Fin 2) :
    ((nativeCoupleForest D hS q).nodeEmbedding
        (GNode.root (nativeCoupleForest D hS q).shape j)).1 = coupleRoot D hS q j := by
  rw [couple_root_node D hS q j]
  unfold coupleRoot
  split_ifs <;> rfl

theorem cplG_eq (g : Fin w → Mom d → ℂ) (q : SourcePair S) :
    Stage1WNoVine.cplG D hS g q = fun j => g (coupleRoot D hS q j).1 := by
  funext j
  have h := congrArg Prod.fst (couple_root_emb D hS q j)
  exact congrArg g h

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

/-- **The frontier-weighted slot family is `slotKerQ` at the weight layers `wLay`.** -/
theorem slotFW_eq_kerQ (L γ δ : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ) (gT : Fin w → Mom d → ℂ)
    (s : ReplacementSlot S) (ts : Fin 2 → ℝ) (k : Mom d) :
    slotFW D hS layer hLayer L γ δ h p gT s ts k =
      slotKerQ D hS layer hLayer L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) p gT s
        (fun i => wLay p (fun b => layer (D.coreBranch hS b).toNode) (argSrc hS s i)) ts k := by
  cases s with
  | inl q =>
    have e := Stage1WNoVine.slotFnNW_fw_couple D hS layer hLayer L γ δ
      (typeProfiles (layeredReconstruction D hS layer hLayer) h) p gT q ts k
    rw [← fwNodeV_eq_fwNode] at e
    refine e.trans ?_
    show coupleLeavesTopR L γ δ p _ _ _ _ _ _ _ k = coupleLeavesTopR L γ δ p _ _ _ _ _ _ _ k
    rw [cplG_eq]
    unfold coupleLeavesTopR
    refine kernelLeavesW_congr_m _ _ _ _ _ _ _ _ _ _ _ _ fun x => ?_
    refine rowTopWeightR_congr_q p _ _ _ _ (fun j y => ?_) x
    fin_cases j
    · exact cplQ_root_factor D hS layer hLayer p _ q 0 y
    · exact cplQ_root_factor D hS layer hLayer p _ q 1 y
  | inr b =>
    have e := Stage1WNoVine.slotFnNW_fw_tree D hS layer hLayer L γ δ
      (typeProfiles (layeredReconstruction D hS layer hLayer) h) p gT b ts k
    rw [← fwNodeV_eq_fwNode] at e
    refine e.trans ?_
    show treeLeavesTop L γ δ p _ _ _ _ _ _ k = treeLeavesTop L γ δ p _ _ _ _ _ _ k
    have hg : Stage1WNoVine.treeG D gT b = gT b.1.1 := congrArg gT (inflatedPosition_index S D.tree b.toNode)
    rw [hg]
    unfold treeLeavesTop
    refine kernelLeavesW_congr_m _ _ _ _ _ _ _ _ _ _ _ _ fun x => ?_
    rw [← rowTopWeightR_const, ← rowTopWeightR_const]
    refine rowTopWeightR_congr_q p _ _ _ _ (fun j y => ?_) x
    fin_cases j
    exact treeQ_root_factor D hS layer hLayer p _ b y

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

/-- The weighted kernel of an ordinary couple is unchanged, for every vector of root weight layers. -/
theorem ordinary_couple_kerQ (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional)
    (qv : Fin 2 → ℕ) (ts : Fin 2 → ℝ) (k : Mom d) :
    slotKerQ h.data (s.chosen_plain ε) layer' hLayer' L γ δ (typeProfiles h.output f) pw g (.inl (s.pairs ε q))
        qv ts k =
      slotKerQ s.data s.plain layer hLayer L γ δ (typeProfiles LG f) pw g (.inl q) qv ts k := by
  show coupleLeavesTopR L γ δ pw (fun j => g (coupleRoot h.data (s.chosen_plain ε) (s.pairs ε q) j).1) (qv 0) (qv 1)
      (nativeCoupleLayered h.data (s.chosen_plain ε) layer' hLayer' (s.pairs ε q))
      (nativeCoupleProfiles h.data (s.chosen_plain ε) (typeProfiles h.output f) (s.pairs ε q)) (ts 0) (ts 1) k =
    coupleLeavesTopR L γ δ pw (fun j => g (coupleRoot s.data s.plain q j).1) (qv 0) (qv 1)
      (nativeCoupleLayered s.data s.plain layer hLayer q)
      (nativeCoupleProfiles s.data s.plain (typeProfiles LG f) q) (ts 0) (ts 1) k
  have hg : (fun j => g (coupleRoot h.data (s.chosen_plain ε) (s.pairs ε q) j).1) =
      fun j => g (coupleRoot s.data s.plain q j).1 :=
    funext fun j => congrArg g (h.ordinary_couple_root_index q hq j)
  rw [hg, native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hq]
  unfold coupleLeavesTopR
  apply kernelLeavesW_congr_inputs
  intro l hl
  obtain ⟨l', he⟩ := h.coupleTransport q hq l
  have hc : h.OrdCorr (nativeLeafAt s.data s.plain (.inl q) l)
      (nativeLeafAt h.data (s.chosen_plain ε) (.inl (s.pairs ε q)) l') :=
    Or.inl ⟨q, hq, l, l', he, rfl, rfl⟩
  calc
    _ = nativeCoupleProfiles h.data (s.chosen_plain ε) (typeProfiles h.output f) (s.pairs ε q) l'.1 :=
      congrArg _ he
    _ = _ := nativeCoupleProfiles_leaf _ _ _ _ _
    _ = _ := (ordinary_typeProfiles h layer hLayer hspec layer' hLayer' hspec' hc f).symm
    _ = _ := (nativeCoupleProfiles_leaf _ _ _ _ _).symm

/-- The weighted kernel of an ordinary tree is unchanged, for every vector of root weight layers. -/
theorem ordinary_tree_kerQ (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower)
    (qv : Fin 2 → ℕ) (ts : Fin 2 → ℝ) (k : Mom d) :
    slotKerQ h.data (s.chosen_plain ε) layer' hLayer' L γ δ (typeProfiles h.output f) pw g (.inr (s.branches ε b))
        qv ts k =
      slotKerQ s.data s.plain layer hLayer L γ δ (typeProfiles LG f) pw g (.inr b) qv ts k := by
  show treeLeavesTop L γ δ pw (g (s.branches ε b).1.1) (qv 0)
      (nativeChainLayered h.data (s.chosen_plain ε) layer' hLayer' (s.branches ε b))
      (nativeChainProfiles h.data (s.chosen_plain ε) (typeProfiles h.output f) (s.branches ε b)) (ts 0) (ts 1) k =
    treeLeavesTop L γ δ pw (g b.1.1) (qv 0) (nativeChainLayered s.data s.plain layer hLayer b)
      (nativeChainProfiles s.data s.plain (typeProfiles LG f) b) (ts 0) (ts 1) k
  rw [s.branches_index ε b, native_tree_eq h layer hLayer hspec layer' hLayer' hspec' b hb]
  unfold treeLeavesTop
  apply kernelLeavesW_congr_inputs
  intro l hl
  let q : NativeLeaf s.data (.inr b) := ⟨l, fun he => not_mem_inputLeaves_chain_lone s.data b l he hl⟩
  obtain ⟨q', he⟩ := h.chainTransport b hb q
  have hc : h.OrdCorr (nativeLeafAt s.data s.plain (.inr b) q)
      (nativeLeafAt h.data (s.chosen_plain ε) (.inr (s.branches ε b)) q') :=
    Or.inr ⟨b, hb, q, q', he, rfl, rfl⟩
  calc
    _ = nativeChainProfiles h.data (s.chosen_plain ε) (typeProfiles h.output f) (s.branches ε b) q'.1.1 :=
      congrArg _ he
    _ = _ := nativeChainProfiles_leaf _ _ _ _ _
    _ = _ := (ordinary_typeProfiles h layer hLayer hspec layer' hLayer' hspec' hc f).symm
    _ = _ := (nativeChainProfiles_leaf _ _ _ _ q).symm

end LF

end WaveTurbulence.Flower.Stage1WVine
