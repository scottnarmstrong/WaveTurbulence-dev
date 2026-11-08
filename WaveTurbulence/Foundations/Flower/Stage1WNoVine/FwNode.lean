/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.WLeaves
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.SlotKer
public import WaveTurbulence.Foundations.Flower.Stage1W.Inputs
public import WaveTurbulence.Foundations.Stage1.Represents.RepBr4
public import WaveTurbulence.Foundations.Stage1.Represents.RepLeaf1

/-! # STAGE1W-O4: the node partition of the frontier weight (row T1)

`fwWeight p g base LG` is the node product of `fwNode LG p g` (`fwWeight_eq_prod`).  For an object embedded in the
garden by address prefixing (the native couples and trees of a reconstruction), the node product over its nodes is
its row weight `rowTopWeightR` with per-root weights `g (tree of the root)` and weight layers `embQ`: the parent layer
of the root in the garden, or the root's own layer at a garden root (whose factor is absent from `fwWeight`)
(`prod_fwNode_embed`).  Hence the weighted native kernels of a reconstruction are `coupleLeavesTopR` /
`treeLeavesTop` (`slotFnNW_fw_couple`, `slotFnNW_fw_tree`), the weight layers are the clock layers away from garden
roots (`cplQ_spec`, `treeQ_spec`), and the frontier exponents of the slots sum to at most `3 · order`
(`sum_slotExp_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence TTree Reg Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.RegRedLeaf WaveTurbulence.LGSpine
  WaveTurbulence.Flower.Stage1W

/-- The frontier node weight of a layered garden (`1` at the roots). -/
def fwNode {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (g : Fin w → Mom d → ℂ) (z : GNode LG.garden.tree)
    (x : Mom d) : ℂ :=
  if z.1.2 ≠ [] then topPsi p (g z.1.1) (LG.layer z) (LG.parentLayer p z) x else 1

theorem fwWeight_eq_prod {P : WTParams} {R : ℕ} (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (base : Mom P.d)
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (LG : LayeredGarden (2 * R))
    (κ : GenDecoration LG.garden P.d roots 0) :
    fwWeight p g base LG κ = ∏ z, fwNode LG p g z (cosetDecoration LG.garden P.L base κ.1 z) := rfl

theorem norm_fwNode_le {w d : ℕ} (LG : LayeredGarden w) (p : ℕ) (g : Fin w → Mom d → ℂ) (cψ : ℝ)
    (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ) (z : GNode LG.garden.tree) (x : Mom d) :
    ‖fwNode LG p g z x‖ ≤ cψ := by
  unfold fwNode topPsi
  split_ifs
  · exact hg _ _
  · simpa using hc
  · simpa using hc

/-- The weight layers of an embedded object. -/
def embQ {v w : ℕ} (LG : LayeredGarden w) (LG' : LayeredGarden v)
    (e : GNode LG'.garden.tree → GNode LG.garden.tree) (r : Fin v → Fin w × TTree.Path) (p : ℕ)
    (j : Fin v) : ℕ :=
  if (r j).2 = [] then LG'.layer (GNode.root LG'.garden.tree j) else LG.parentLayer p (e (GNode.root LG'.garden.tree j))

section Embed

variable {v w d : ℕ} (LG : LayeredGarden w) (LG' : LayeredGarden v)
    (e : GNode LG'.garden.tree → GNode LG.garden.tree) (r : Fin v → Fin w × TTree.Path)
    (he : ∀ a, (e a).1 = ((r a.1.1).1, (r a.1.1).2 ++ a.1.2)) (hl : ∀ a, LG'.layer a = LG.layer (e a))

include he hl in
theorem fwNode_embed (p : ℕ) (g : Fin w → Mom d → ℂ) (a : GNode LG'.garden.tree) (x : Mom d) :
    fwNode LG p g (e a) x =
      topPsi p (g (r a.1.1).1) (LG'.layer a) (rowParentLayer LG' (embQ LG LG' e r p) a) x := by
  have hi : (e a).1.1 = (r a.1.1).1 := by rw [he]
  unfold fwNode rowParentLayer
  rw [hl a]
  by_cases ha : a.1.2 = []
  · have hea : (e a).1.2 = (r a.1.1).2 := by rw [he]; simp [ha]
    have hra : a = GNode.root LG'.garden.tree a.1.1 := Subtype.ext (Prod.ext rfl ha)
    rw [if_pos ha]
    unfold embQ
    by_cases hr : (r a.1.1).2 = []
    · rw [if_pos hr]
      have hn : ¬ ((e a).1.2 ≠ []) := by rw [hea, hr]; simp
      rw [if_neg hn, ← hra, hl a]
      unfold topPsi
      rw [if_neg (by omega)]
    · rw [if_neg hr]
      have hn : (e a).1.2 ≠ [] := by rw [hea]; exact hr
      rw [if_pos hn, hi, ← hra]
  · have hea : (e a).1.2 ≠ [] := by rw [he]; simp [ha]
    have hpar : LG.parentLayer p (e a) = LG'.parentLayer 0 a := by
      rw [LFTwist.parentLayer_nonroot LG p (e a) hea, LFTwist.parentLayer_nonroot LG' 0 a ha, hl]
      congr 1
      apply Subtype.ext
      show ((e a).1.1, (e a).1.2.dropLast) = (e (GNode.parent a ha).toNode).1
      rw [he (GNode.parent a ha).toNode, he a, List.dropLast_append_of_ne_nil ha]
      rfl
    rw [if_pos hea, if_neg ha, hi, hpar]

include he hl in
theorem prod_fwNode_embed (p : ℕ) (g : Fin w → Mom d → ℂ) (k : GNode LG'.garden.tree → Mom d) :
    ∏ a, fwNode LG p g (e a) (k a) = rowTopWeightR p (fun j => g (r j).1) LG' (embQ LG LG' e r p) k := by
  unfold rowTopWeightR
  exact Finset.prod_congr rfl fun a _ => fwNode_embed LG LG' e r he hl p g a (k a)

include he in
/-- The nodes that can carry a frontier factor are garden-nonroot nodes. -/
theorem card_embNodes_le (p : ℕ) :
    (Finset.univ.filter fun x : GNode LG'.garden.tree =>
        x.1.2 ≠ [] ∨ embQ LG LG' e r p x.1.1 ≠ LG'.layer (GNode.root LG'.garden.tree x.1.1)).card ≤
      (Finset.univ.filter fun x : GNode LG'.garden.tree => (e x).1.2 ≠ []).card := by
  refine Finset.card_le_card fun x hx => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rw [he]
  rcases hx with hx | hx
  · simp [hx]
  · by_cases hr : (r x.1.1).2 = []
    · unfold embQ at hx
      rw [if_pos hr] at hx
      exact absurd rfl hx
    · simp [hr]

end Embed

/-! ### The native couples and trees of a reconstruction -/

section Native

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-- The per-arm weights of a couple slot. -/
def cplG (g : Fin w → Mom d → ℂ) (p' : SourcePair S) : Fin 2 → Mom d → ℂ :=
  fun j => g ((nativeCoupleForest D hS p').root j).1.1

/-- The weight layers of a couple slot. -/
def cplQ (p : ℕ) (p' : SourcePair S) : Fin 2 → ℕ :=
  embQ (layeredReconstruction D hS layer hLayer) (nativeCoupleLayered D hS layer hLayer p')
    (nativeCoupleForest D hS p').nodeEmbedding (fun j => ((nativeCoupleForest D hS p').root j).1) p

/-- The weight of a tree slot. -/
def treeG (g : Fin w → Mom d → ℂ) (b : GBranch S.tree) : Mom d → ℂ :=
  g (inflatedPosition S D.tree b.toNode).1

/-- The weight layer of a tree slot. -/
def treeQ (p : ℕ) (b : GBranch S.tree) : ℕ :=
  embQ (layeredReconstruction D hS layer hLayer) (nativeChainLayered D hS layer hLayer b)
    (chainContextNode D hS b) (fun _ => inflatedPosition S D.tree b.toNode) p 0

theorem fin2_vec (f : Fin 2 → ℕ) : f = ![f 0, f 1] := by
  funext j; fin_cases j <;> rfl

theorem fin1_vec (f : Fin 1 → ℕ) : f = ![f 0] := by
  funext j; fin_cases j; rfl

/-- **The weighted native couple kernel is `coupleLeavesTopR`.** -/
theorem slotFnNW_fw_couple (L γ δ : ℝ) (H : LeafProfiles w d) (p : ℕ) (g : Fin w → Mom d → ℂ)
    (p' : SourcePair S) (ts : Fin 2 → ℝ) (k : Mom d) :
    slotFnNW D hS L γ δ H (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer (.inl p') ts k =
      coupleLeavesTopR L γ δ p (cplG D hS g p') (cplQ D hS layer hLayer p p' 0) (cplQ D hS layer hLayer p p' 1)
        (nativeCoupleLayered D hS layer hLayer p') (nativeCoupleProfiles D hS H p') (ts 0) (ts 1) k := by
  have hA : (fun a : GNode (nativeCoupleLayered D hS layer hLayer p').garden.tree =>
      H ((nativeCoupleForest D hS p').nodeEmbedding a).1) = fun a => nativeCoupleProfiles D hS H p' a.1 := by
    funext a
    unfold nativeCoupleProfiles
    split_ifs with h
    · rfl
    · exact absurd a.2 h
  have hm : (fun k' : GNode (nativeCoupleLayered D hS layer hLayer p').garden.tree → Mom d =>
      ∏ a, fwNode (layeredReconstruction D hS layer hLayer) p g ((nativeCoupleForest D hS p').nodeEmbedding a) (k' a)) =
      rowTopWeightR p (cplG D hS g p') (nativeCoupleLayered D hS layer hLayer p')
        ![cplQ D hS layer hLayer p p' 0, cplQ D hS layer hLayer p p' 1] := by
    funext k'
    refine (prod_fwNode_embed (layeredReconstruction D hS layer hLayer) (nativeCoupleLayered D hS layer hLayer p')
      (fun a => (nativeCoupleForest D hS p').nodeEmbedding a) (fun j => ((nativeCoupleForest D hS p').root j).1)
      (fun a => rfl) (fun a => rfl) p g k').trans ?_
    rw [← fin2_vec (cplQ D hS layer hLayer p p')]
    rfl
  show kernelNodeW L γ δ (nativeCoupleLayered D hS layer hLayer p')
      (fun a => H ((nativeCoupleForest D hS p').nodeEmbedding a).1)
      (fun k' => ∏ a, fwNode (layeredReconstruction D hS layer hLayer) p g
        ((nativeCoupleForest D hS p').nodeEmbedding a) (k' a))
      (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 = _
  rw [hA, hm]
  rfl

/-- **The weighted native tree kernel is `treeLeavesTop`.** -/
theorem slotFnNW_fw_tree (L γ δ : ℝ) (H : LeafProfiles w d) (p : ℕ) (g : Fin w → Mom d → ℂ)
    (b : GBranch S.tree) (ts : Fin 2 → ℝ) (k : Mom d) :
    slotFnNW D hS L γ δ H (fwNode (layeredReconstruction D hS layer hLayer) p g) layer hLayer (.inr b) ts k =
      treeLeavesTop L γ δ p (treeG D g b) (treeQ D hS layer hLayer p b)
        (nativeChainLayered D hS layer hLayer b) (nativeChainProfiles D hS H b) (ts 0) (ts 1) k := by
  have hA : (fun a : GNode (nativeChainLayered D hS layer hLayer b).garden.tree =>
      H (chainContextNode D hS b a).1) = fun a => nativeChainProfiles D hS H b a.1 := by
    funext a
    unfold nativeChainProfiles
    split_ifs with h
    · rfl
    · exact absurd a.2 h
  have hm : (fun k' : GNode (nativeChainLayered D hS layer hLayer b).garden.tree → Mom d =>
      ∏ a, fwNode (layeredReconstruction D hS layer hLayer) p g (chainContextNode D hS b a) (k' a)) =
      rowTopWeight p (treeG D g b) (nativeChainLayered D hS layer hLayer b) ![treeQ D hS layer hLayer p b] := by
    funext k'
    refine (prod_fwNode_embed (layeredReconstruction D hS layer hLayer) (nativeChainLayered D hS layer hLayer b)
      (chainContextNode D hS b) (fun _ => inflatedPosition S D.tree b.toNode)
      (fun a => rfl) (fun a => rfl) p g k').trans ?_
    rw [← rowTopWeightR_const]
    have e : embQ (layeredReconstruction D hS layer hLayer) (nativeChainLayered D hS layer hLayer b)
        (chainContextNode D hS b) (fun _ => inflatedPosition S D.tree b.toNode) p =
        ![treeQ D hS layer hLayer p b] := fin1_vec _
    rw [e]
    rfl
  show kernelNodeW L γ δ (nativeChainLayered D hS layer hLayer b)
      (fun a => H (chainContextNode D hS b a).1)
      (fun k' => ∏ a, fwNode (layeredReconstruction D hS layer hLayer) p g (chainContextNode D hS b a) (k' a))
      (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 = _
  rw [hA, hm]
  rfl

/-- Away from garden roots the weight layers are the clock layers; at a garden root, the root layer. -/
theorem cplQ_spec (p : ℕ) (p' : SourcePair S) (j : Fin 2) :
    cplQ D hS layer hLayer p p' j =
        Represents.clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (Represents.argSrc hS (.inl p') j) ∨
      (cplQ D hS layer hLayer p p' j =
          (nativeCoupleLayered D hS layer hLayer p').layer
            (GNode.root (nativeCoupleLayered D hS layer hLayer p').garden.tree j) ∧
        Represents.clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (Represents.argSrc hS (.inl p') j) = p) := by
  set ν : GNode S.tree := if j = 0 then (p'.firstLeaf hS).toNode else (p'.secondLeaf hS).toNode with hν
  have hcl : Represents.argSrc hS (.inl p') j = Represents.clkOfNode S ν := by
    fin_cases j <;> simp [Represents.argSrc, hν]
  rw [hcl]
  have hroot := Represents.couple_root_node D hS p' j
  have hpl := Represents.parentLayer_inflated D hS layer hLayer p ν
    ((nativeCoupleForest D hS p').nodeEmbedding (GNode.root (nativeCoupleForest D hS p').shape j)) hroot
  unfold cplQ embQ
  by_cases hr : (((nativeCoupleForest D hS p').root j).1).2 = []
  · right
    rw [if_pos hr]
    refine ⟨rfl, ?_⟩
    rw [← hpl]
    unfold LayeredGarden.parentLayer
    rw [if_pos]
    show (((nativeCoupleForest D hS p').root j).1).2 ++ [] = []
    rw [hr]; rfl
  · left
    rw [if_neg hr]
    exact hpl

theorem treeQ_spec (p : ℕ) (b : GBranch S.tree) :
    treeQ D hS layer hLayer p b =
        Represents.clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (Represents.argSrc hS (.inr b) 0) ∨
      (treeQ D hS layer hLayer p b =
          (nativeChainLayered D hS layer hLayer b).layer
            (GNode.root (nativeChainLayered D hS layer hLayer b).garden.tree 0) ∧
        Represents.clkLayer p (fun b => layer (D.coreBranch hS b).toNode) (Represents.argSrc hS (.inr b) 0) = p) := by
  have hcl : Represents.argSrc hS (.inr b) 0 = Represents.clkOfNode S b.toNode := by simp [Represents.argSrc]
  rw [hcl]
  have hroot := Represents.tree_root_node D hS b
  have hpl := Represents.parentLayer_inflated D hS layer hLayer p b.toNode
    (chainContextNode D hS b (GNode.root (decodedTree (D.tree b) (nodeSign S.sig b.1)).tree 0)) hroot
  unfold treeQ embQ
  by_cases hr : (inflatedPosition S D.tree b.toNode).2 = []
  · right
    rw [if_pos hr]
    refine ⟨rfl, ?_⟩
    rw [← hpl]
    unfold LayeredGarden.parentLayer
    rw [if_pos]
    show (inflatedPosition S D.tree b.toNode).2 ++ [] = []
    rw [hr]; rfl
  · left
    rw [if_neg hr]
    exact hpl

/-! ### The frontier exponents -/

/-- The garden-nonroot nodes of a slot. -/
def slotNr (s : ReplacementSlot S) : ℕ :=
  (Finset.univ.filter fun a : NativeNode D s => (nativeNodeAt D hS s a).1.2 ≠ []).card

theorem sum_slotNr : ∑ s, slotNr D hS s = 3 * (D.garden hS).order := by
  have h1 : (Finset.univ.filter fun z : GNode (D.forest hS) => z.1.2 ≠ []).card =
      ∑ s, slotNr D hS s := by
    rw [Finset.card_filter]
    rw [← (nativeNodeEquiv D hS).sum_comp, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold slotNr
    rw [Finset.card_filter]
    rfl
  rw [← h1]
  exact card_nonroot (D.forest hS)

end Native

end WaveTurbulence.Flower.Stage1WNoVine
