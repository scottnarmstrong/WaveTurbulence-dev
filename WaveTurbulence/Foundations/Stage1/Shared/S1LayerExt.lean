/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.LFConstruction
public import WaveTurbulence.Foundations.Molecule.LFTwist.TreeCollapseCanonical
import Mathlib.Tactic

/-!
# Collapse after coherent reinsertion is the identity (tree part)

Extensionality of layered gardens through `layerAt` and the statement that collapsing a
reinserted regular tree gives back the tree-free layered garden it was inserted into.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Links WaveTurbulence.LFTwist

variable {w : ℕ}

theorem layered_ext {LG LH : LayeredGarden w} (hg : LG.garden = LH.garden)
    (hl : ∀ x, layerAt LG x = layerAt LH x) : LG = LH := by
  rcases LG with ⟨G, l, hl'⟩
  rcases LH with ⟨H, m, hm'⟩
  change G = H at hg
  subst hg
  congr
  funext n
  have := hl n.1
  rwa [layerAt_node ⟨G, l, hl'⟩ n, layerAt_node ⟨G, m, hm'⟩ n] at this

/-- Two layered gardens that are both `LG` with the subtree at `n` moved up to `a` (the region of
`LG` between `a` and `n` removed) have the same layer function. -/
theorem layerAt_eq_of_outAgreeT {LG C M : LayeredGarden w} {a n : Fin w × Path} (ha : Under a n)
    (hC : OutAgreeT LG C a n a) (hM : OutAgreeT LG M a n a) (y : Fin w × Path) :
    layerAt C y = layerAt M y := by
  have hy : ¬ InTree a a y := fun h => h.2 h.1
  have hz : ¬ InTree a n (shiftAddr a n y) := out_shift hy
  have hs : shiftAddr n a (shiftAddr a n y) = y := shift_shift ha hy
  have e1 := hC.layer _ hz
  have e2 := hM.layer _ hz
  rw [hs] at e1 e2
  exact e1.symm.trans e2

/-- **Collapsing a reinserted regular tree gives back the tree-free layered garden** (garden decoded
by the erased reconstruction data, layers agreeing outside the region). -/
theorem collapse_insert_tree {S : Garden w} (E : ReconstructionData S) (hS : S.IsPlain)
    (LG M : LayeredGarden w) (hd : E.Decodes hS LG.garden) (b : GBranch S.tree)
    (hM : (E.eraseTree b).Decodes hS M.garden) {ζ : ℤˣ} {t : TTree}
    (hemb : ChainEmb M.garden .nil ζ (inflatedPosition S (E.eraseTree b).tree b.toNode) t)
    (hout : OutAgreeT M LG (inflatedPosition S (E.eraseTree b).tree b.toNode)
      (addrExt (inflatedPosition S (E.eraseTree b).tree b.toNode) RegChain.nil.lonePath)
      (addrExt (inflatedPosition S (E.eraseTree b).tree b.toNode) (E.tree b).lonePath)) :
    collapsePairedTreeLayered LG (E.decoded_chain_isSubPairedTree hS hd b) = M := by
  have hpos : inflatedPosition S E.tree b.toNode = inflatedPosition S (E.eraseTree b).tree b.toNode :=
    (E.eraseTree_position_at b).symm
  have hc := eraseTree_collapse_decodes E hS hd b
  have hgar : (collapsePairedTreeLayered LG (E.decoded_chain_isSubPairedTree hS hd b)).garden = M.garden :=
    rawOfGarden_injective_plain hc.1 hM.1 (hc.2.symm.trans hM.2)
  apply layered_ext hgar
  have hC := collapsePairedTree_outAgree LG (E.decoded_chain_isSubPairedTree hS hd b)
  have hC' : OutAgreeT LG (collapsePairedTreeLayered LG (E.decoded_chain_isSubPairedTree hS hd b))
      (inflatedPosition S (E.eraseTree b).tree b.toNode)
      (addrExt (inflatedPosition S (E.eraseTree b).tree b.toNode) (E.tree b).lonePath)
      (inflatedPosition S (E.eraseTree b).tree b.toNode) := by
    rw [← hpos]
    exact hC
  have hM' := hout.symm hemb
  simp only [RegChain.lonePath, addrExt_nil] at hM'
  intro y
  exact layerAt_eq_of_outAgreeT (under_ext _ _) hC' hM' y

/-- A trivial embedded couple leaves no branching node below either root. -/
theorem no_branch_under_triv {G : Garden w} {a b : Fin w × Path} (h : Embeds G .triv a b)
    (c : GBranch G.tree) : ¬ Under a c.1 ∧ ¬ Under b c.1 := by
  have key : ∀ (x : Fin w × Path) (t : TTree), x.2 ∈ (G.tree x.1).nodes → (G.tree x.1).subtreeAt x.2 = t →
      t.branching = ∅ → ¬ Under x c.1 := by
    intro x t hx ht hb ⟨h1, h2⟩
    obtain ⟨s, hs⟩ := h2
    have hc : c.1.2 ∈ (G.tree c.1.1).branching := c.2
    rw [← hs, ← h1] at hc
    have := ((mem_subtreeAt (G.tree x.1) x.2 hx s).2.2).mpr hc
    rw [ht, hb] at this
    simp at this
  refine ⟨key a _ h.nodeA h.treeA ?_, key b _ h.nodeB h.treeB ?_⟩ <;>
    simp [RegCpl.trees, TTree.branching]

/-- A layered garden that is the minimum-parent extension of its own branch layers and has the same
garden and branch layers as a canonical plain layered garden is that garden. -/
theorem layered_eq_of_branches {C N : LayeredGarden w} (p : ℕ) (hg : C.garden = N.garden)
    (hN : N.CanonCriterion p) (hplain : N.garden.IsPlain)
    (hC : C.layer = extendBranchLayers C.garden (fun c => C.layer c.toNode) p) :
    (∀ c : GBranch C.garden.tree, C.layer c.toNode = N.layer (GBranch.toNode (tree := N.garden.tree) ⟨c.1, hg ▸ c.2⟩)) →
    C = N := by
  intro hb
  rcases C with ⟨G, l, hl⟩
  rcases N with ⟨H, m, hm⟩
  change G = H at hg
  subst hg
  have e := extendBranchLayers_eq_canonical ⟨G, m, hm⟩ p hN hplain
  have hf : (fun c : GBranch G.tree => l c.toNode) = fun c => m c.toNode := funext hb
  change l = extendBranchLayers G (fun c => l c.toNode) p at hC
  change extendBranchLayers G (fun b => m b.toNode) p = m at e
  congr 1
  rw [hC, hf, e]

/-- **Collapsing a reinserted regular couple gives back the couple-free canonical layered garden.** -/
theorem collapse_insert_couple {S : Garden w} (F : ReconstructionData S) (hS : S.IsPlain)
    (T N : LayeredGarden w) (hd : F.Decodes hS T.garden) (q : SourcePair S) (hq : F.couple q ≠ .triv)
    (hN : (F.eraseCouple q).Decodes hS N.garden) (p : ℕ)
    (hcT : T.CanonCriterion p) (hcN : N.CanonCriterion p)
    (hemb : Embeds N.garden .triv (inflatedPosition S F.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S F.tree (q.secondLeaf hS).toNode))
    (hout : OutAgree N T (inflatedPosition S F.tree (q.firstLeaf hS).toNode)
      (inflatedPosition S F.tree (q.secondLeaf hS).toNode)) :
    collapseCoupleLayered T (F.decoded_couple_isSubCouple hS hd q) p = N := by
  have hc := F.eraseCouple_collapse_decodes hS hd q hq
  have hgar : (collapseCoupleLayered T (F.decoded_couple_isSubCouple hS hd q) p).garden = N.garden :=
    rawOfGarden_injective_plain hc.1 hN.1 (hc.2.symm.trans hN.2)
  have hC := collapseCouple_outAgree T (F.decoded_couple_isSubCouple hS hd q) p hcT hd.1
  refine layered_eq_of_branches p hgar hcN hN.1 ?_ ?_
  · have hf : (fun c : GBranch (collapseCoupleGarden (F.decoded_couple_isSubCouple hS hd q)).tree =>
        (collapseCoupleLayered T (F.decoded_couple_isSubCouple hS hd q) p).layer c.toNode) =
        fun c => T.layer (collapseCoupleBranchEmbedding (F.decoded_couple_isSubCouple hS hd q) c).toNode :=
      funext fun c => collapseCoupleLayered_branch T _ p c
    change (collapseCoupleLayered T (F.decoded_couple_isSubCouple hS hd q) p).layer =
      extendBranchLayers (collapseCoupleGarden (F.decoded_couple_isSubCouple hS hd q)) (fun c =>
        (collapseCoupleLayered T (F.decoded_couple_isSubCouple hS hd q) p).layer c.toNode) p
    rw [hf]
    rfl
  · intro c
    have hcN' : (⟨c.1, hgar ▸ c.2⟩ : GBranch N.garden.tree).1 = c.1 := rfl
    have hnr := no_branch_under_triv hemb ⟨c.1, hgar ▸ c.2⟩
    have hreg : ¬ InRegion (inflatedPosition S F.tree (q.firstLeaf hS).toNode)
        (inflatedPosition S F.tree (q.secondLeaf hS).toNode) c.1 := by
      rintro (h | h)
      · exact hnr.1 h
      · exact hnr.2 h
    have e1 := layerAt_node (collapseCoupleLayered T (F.decoded_couple_isSubCouple hS hd q) p) c.toNode
    have e2 := layerAt_node N (GBranch.toNode (tree := N.garden.tree) ⟨c.1, hgar ▸ c.2⟩)
    rw [← e1, ← e2]
    change layerAt _ c.1 = layerAt N c.1
    rw [← hC.layer c.1 hreg, hout.layer c.1 hreg]

/-- `collapse_insert_tree` with the erased data and the inserted code named. -/
theorem collapse_insert_tree' {S : Garden w} (E : ReconstructionData S) (hS : S.IsPlain)
    (LG M : LayeredGarden w) (hd : E.Decodes hS LG.garden) (b : GBranch S.tree)
    (Mdat : ReconstructionData S) (hMd : E.eraseTree b = Mdat) (X : RegChain) (hX : E.tree b = X)
    (hM : Mdat.Decodes hS M.garden) {ζ : ℤˣ} {t : TTree}
    (hemb : ChainEmb M.garden .nil ζ (inflatedPosition S Mdat.tree b.toNode) t)
    (hout : OutAgreeT M LG (inflatedPosition S Mdat.tree b.toNode)
      (addrExt (inflatedPosition S Mdat.tree b.toNode) RegChain.nil.lonePath)
      (addrExt (inflatedPosition S Mdat.tree b.toNode) X.lonePath)) :
    collapsePairedTreeLayered LG (E.decoded_chain_isSubPairedTree hS hd b) = M := by
  subst hMd
  subst hX
  exact collapse_insert_tree E hS LG M hd b hM hemb hout

/-- Two canonical plain layered gardens with the same garden that agree outside two trivial leaf
roots are equal. -/
theorem layered_eq_of_canonical_outAgree {C N : LayeredGarden w} {a b : Fin w × Path} (p : ℕ)
    (hCc : C.CanonCriterion p) (hNc : N.CanonCriterion p) (hCp : C.garden.IsPlain)
    (hNp : N.garden.IsPlain) (hg : C.garden = N.garden) (hout : OutAgree N C a b)
    (hemb : Embeds N.garden .triv a b) : C = N := by
  refine layered_eq_of_branches p hg hNc hNp (extendBranchLayers_eq_canonical C p hCc hCp).symm ?_
  intro c
  have hnr := no_branch_under_triv hemb ⟨c.1, hg ▸ c.2⟩
  have hreg : ¬ InRegion a b c.1 := by
    rintro (h | h)
    · exact hnr.1 h
    · exact hnr.2 h
  have e1 := layerAt_node C c.toNode
  have e2 := layerAt_node N (GBranch.toNode (tree := N.garden.tree) ⟨c.1, hg ▸ c.2⟩)
  rw [← e1, ← e2]
  exact (hout.layer c.1 hreg).symm

end WaveTurbulence.Stage1
