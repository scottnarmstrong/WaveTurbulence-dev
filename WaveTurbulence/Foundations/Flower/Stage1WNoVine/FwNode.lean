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
