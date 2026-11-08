/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoCore
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoChain
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCore3

/-! # B3s-HELPER3 B4 (pattern R-core 3): the pattern pins are common to the run class

The pattern twin of B3s's R-core (`MkSlots/IntCore2`, `IntCore3`: `member_cfp_iff`, `member_fixCap`,
`member_fix_unit`). For a member `y` of the run class of the representative `a` at a marking (shape
`Φ = memShape a mk y hy`), every pattern `pat`:

* **`member_fixCap_pat`**: the pins `fixCap … pat` of `y` at the cores of the `G_sb` atoms are the pins
  `fixAt J pat t s a (mk a.prime)` of the piece;
* **`member_fix_unit_pat`**: no core of an atom of a unit of `y` is pinned (`hU` of the member's pinned VINE-B♯).

The only hypothesis beyond B3s's (`hG`, `hcapA`, `hcapY`) is the representative's `hrepUP`: no core of an atom of a
unit of `a` is pinned — `PatGeoU.hU_rep_pat_recon` (every pattern; it implies B3s's `hrepU`).

Ingredients: `fixCap_congr` (four predicates), the chain transport `memShape_lonePath_nil_iff`, B3s's
`member_cfp_iff`/`member_unit_not_cfp`/`member_hinge_iff`, the native couple R-SLOT `memShape_nativeCouple` (for
`RootCfpG`), and the crown of a unit (`crown_exists`, `crown_parent`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntCore WaveTurbulence.Flower.MkSlots.IntRest

namespace WaveTurbulence.Flower.MkSlotsB

theorem getLast_of_eq {l l' : List (Fin 3)} {k : Fin 3} (h : l = l' ++ [k]) (hne : l ≠ []) : l.getLast hne = k := by
  subst h
  exact List.getLast_concat

/-! ## Through a splice shape -/

section Shape
variable {w : ℕ} {S : Garden w} {Ju : Type} [Fintype Ju] [DecidableEq Ju] {blk : Ju → CLBlock S}
  {G : Garden w} (Φ : SpliceShape blk G)

/-- A `G_sb` branch is a root iff its old name is a skeleton root. -/
theorem br_root_iff (c : GBranch G.tree) : (Φ.br c).1.2 = [] ↔ c.1.2 = [] := by
  constructor
  · intro h
    have h1 : Φ.node c.toNode = Φ.node (GNode.root G.tree c.1.1) := by
      rw [Φ.root, ← Φ.br_node]
      apply Subtype.ext
      exact Prod.ext (br_fst Φ c) h
    exact congrArg (fun x : GNode G.tree => x.1.2) (Φ.inj h1)
  · intro h
    have h1 : c.toNode = GNode.root G.tree c.1.1 := Subtype.ext (Prod.ext rfl h)
    have h2 := congrArg Φ.node h1
    rw [Φ.root, ← Φ.br_node] at h2
    exact congrArg (fun x : GNode S.tree => x.1.2) h2

/-- The skeleton parent of the old name of a non-root `G_sb` branch: the old name of its `G_sb` parent (with the same
last step) when that is not a hinge, an atom of the unit when it is. -/
theorem br_parent_cases (c : GBranch G.tree) (hc : c.1.2 ≠ []) :
    ∃ hb : (Φ.br c).1.2 ≠ [],
      ((∀ j, Φ.br (c.toNode.parent hc) ≠ (blk j).upper) →
        (Φ.br c).toNode.parent hb = Φ.br (c.toNode.parent hc) ∧ (Φ.br c).1.2.getLast hb = c.1.2.getLast hc) ∧
      (∀ j, Φ.br (c.toNode.parent hc) = (blk j).upper → (Φ.br c).toNode.parent hb ∈ (blk j).atoms) := by
  have hb : (Φ.br c).1.2 ≠ [] := fun h => hc ((br_root_iff Φ c).mp h)
  refine ⟨hb, fun hnh => ?_, fun j hj => ?_⟩
  · have hn := Φ.child (c.toNode.parent hc) (c.1.2.getLast hc) hnh
    rw [show (c.toNode.parent hc).child (c.1.2.getLast hc) = c.toNode from Skeleton.child_parent c.toNode hc,
      ← Φ.br_node] at hn
    have hv := congrArg Subtype.val hn
    have h1 : (Φ.br c).1.1 = (Φ.br (c.toNode.parent hc)).1.1 := by have h := congrArg Prod.fst hv; exact h
    have h2 : (Φ.br c).1.2 = (Φ.br (c.toNode.parent hc)).1.2 ++ [c.1.2.getLast hc] := by
      have h := congrArg Prod.snd hv; exact h
    refine ⟨Subtype.ext ?_, getLast_of_eq h2 hb⟩
    show ((Φ.br c).1.1, (Φ.br c).1.2.dropLast) = _
    rw [h1, h2, List.dropLast_concat]
  · have hcr := Φ.crown (c.toNode.parent hc) j hj (c.1.2.getLast hc)
    rw [show (c.toNode.parent hc).child (c.1.2.getLast hc) = c.toNode from Skeleton.child_parent c.toNode hc,
      ← Φ.br_node] at hcr
    obtain ⟨v, hv, i, hvi⟩ := crown_parent (blk j) hcr
    have hpv : (Φ.br c).toNode.parent hb = v := by
      have hv' := congrArg Subtype.val hvi
      have h1 : v.1.1 = (Φ.br c).1.1 := by have h := congrArg Prod.fst hv'; exact h
      have h2 : v.1.2 ++ [i] = (Φ.br c).1.2 := by have h := congrArg Prod.snd hv'; exact h
      apply Subtype.ext
      show ((Φ.br c).1.1, (Φ.br c).1.2.dropLast) = v.1
      rw [← h1, ← h2, List.dropLast_concat]
    rw [hpv]
    exact hv

/-- The tree of side `j` of the native couple of the image of a `G_sb` pair. -/
def inJG (J : Finset (Fin w)) (hG : G.IsPlain) (qG : SourcePair G) (j : Fin 2) : Prop :=
  (if j = 0 then (qG.firstLeaf hG).1.1 else (qG.secondLeaf hG).1.1) ∈ J

theorem leaf_fst' (ℓ : GLeaf G.tree) : (Φ.leaf ℓ).1.1 = ℓ.1.1 := by
  have h := Φ.tree_eq ℓ.toNode
  rw [← Φ.leaf_node] at h
  exact h

/-- **The native couple root attached at the image of a `G_sb` leaf**, through the shape. -/
theorem cfp_attached_leaf_iff (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w)) (hG : G.IsPlain) (ℓ : GLeaf G.tree) :
    (∃ C : GBranch (D.forest hS), C.toNode = attachedNode D hS (Φ.leaf ℓ).toNode ∧
        IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C) ↔
      RootCfpG (decodedCouple (D.couple (pairOfLeaf S hS (Φ.leaf ((pairOfLeaf G hG ℓ).firstLeaf hG)))))
        (if (pairOfLeaf G hG ℓ).firstLeaf hG = ℓ then 0 else 1) (inJG J hG (pairOfLeaf G hG ℓ)) := by
  have hq := pairOfLeaf_shape_leaf Φ hS hG ℓ
  have hside := sideOf_shape_leaf Φ hS hG ℓ
  have hroot := root_sideOf D hS (Φ.leaf ℓ)
  have hinJ : (fun j => ((nativeCoupleForest D hS (pairOfLeaf S hS (Φ.leaf ℓ))).root j).1.1 ∈ J) =
      inJG J hG (pairOfLeaf G hG ℓ) := by
    funext j
    rw [hq]
    unfold inJG
    fin_cases j
    · show ((inflatedPosition S D.tree ((pairOfLeaf S hS (Φ.leaf ((pairOfLeaf G hG ℓ).firstLeaf hG))).firstLeaf
        hS).toNode).1 ∈ J) = _
      rw [inflatedPosition_index, Φ.iota_first hS hG]
      show ((Φ.leaf ((pairOfLeaf G hG ℓ).firstLeaf hG)).1.1 ∈ J) = _
      rw [leaf_fst' Φ]
      simp
    · show ((inflatedPosition S D.tree ((pairOfLeaf S hS (Φ.leaf ((pairOfLeaf G hG ℓ).firstLeaf hG))).secondLeaf
        hS).toNode).1 ∈ J) = _
      rw [inflatedPosition_index, Φ.iota_second hS hG]
      show ((Φ.leaf ((pairOfLeaf G hG ℓ).secondLeaf hG)).1.1 ∈ J) = _
      rw [leaf_fst' Φ]
      simp
  constructor
  · rintro ⟨C, hC, hc⟩
    have h := (cfp_nativeRoot_iff D hS layer hLayer J _ _ C (hC.trans hroot.symm)).mp hc
    rw [hinJ, hside, hq] at h
    exact h
  · intro h
    rw [← hq, ← hside, ← hinJ] at h
    obtain ⟨-, ℓ'', hs'', hl'', -⟩ := id h
    have hne'' : ℓ''.1.2 ≠ [] := fun h0 => by rw [h0] at hl''; simp at hl''
    let E := nativeCoupleForest D hS (pairOfLeaf S hS (Φ.leaf ℓ))
    let c0 : GBranch E.shape := GNode.parent (tree := E.shape) (GLeaf.toNode (tree := E.shape) ℓ'') hne''
    let C := subforestBranchEmbedding E c0
    have hCn : C.toNode = attachedNode D hS (Φ.leaf ℓ).toNode := by
      rw [← hroot]
      apply Subtype.ext
      show ((E.root c0.1.1).1.1, (E.root c0.1.1).1.2 ++ c0.1.2) = (E.root (sideOf hS (Φ.leaf ℓ))).1
      have e1 : c0.1.1 = sideOf hS (Φ.leaf ℓ) := hs''
      have e2 : c0.1.2 = [] := by
        show ℓ''.1.2.dropLast = []
        obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hl''
        rw [hk]; rfl
      rw [e1, e2, List.append_nil]
    exact ⟨C, hCn, (cfp_nativeRoot_iff D hS layer hLayer J _ _ C (hCn.trans hroot.symm)).mpr h⟩

end Shape

end WaveTurbulence.Flower.MkSlotsB
