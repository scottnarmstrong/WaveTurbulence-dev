/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.GluedConservation
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CodePairLabels
public import WaveTurbulence.Foundations.RegStruct.FrameAddressMap

/-! # Every native raw matching edge is respected by the glued labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg Reg.Skeleton

theorem nativeCoupleGarden_decodes {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) : (D.couple p).Decodes (nativeCoupleGarden D hS p) := by
  have he : nativeCoupleGarden D hS p = decodedCouple (D.couple p) := nativeCoupleGarden_eq D hS p
  rw [he]
  exact decodedCouple_decodes _

theorem coupleContextNode_val {w : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (p : SourcePair S) (a : GNode (decodedCouple (D.couple p)).tree) :
    ((nativeCoupleForest D hS p).nodeEmbedding a).1 =
      frameAddress (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
        (inflatedPosition S D.tree (p.secondLeaf hS).toNode) a.1 := by
  obtain ⟨⟨j,q⟩,hq⟩ := a
  fin_cases j <;> rfl

theorem glueRelativeLabels_couple_edge {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (p : SourcePair S)
    (q : Pair w) (hq : q ∈ (D.couple p).pairsAt (inflatedPosition S D.tree (p.firstLeaf hS).toNode)
      (inflatedPosition S D.tree (p.secondLeaf hS).toNode))
    (x y : GNode (D.forest hS)) (hx : x.1 = q.1) (hy : y.1 = q.2) :
    glueRelativeLabels D hS κ ρ x = glueRelativeLabels D hS κ ρ y := by
  rw [pairsAt_frameAddress] at hq
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hq
  let E := nativeCoupleForest D hS p
  let H := nativeCoupleGarden D hS p
  let η := glueRelativeLabels D hS κ ρ
  let u : GLeaf H.tree := ⟨r.1,(decodedCouple_pairs_valid (D.couple p) r hr).1⟩
  let v : GLeaf H.tree := ⟨r.2,(decodedCouple_pairs_valid (D.couple p) r hr).2⟩
  have hX : E.nodeEmbedding u.toNode = x := Subtype.ext
    ((coupleContextNode_val D hS p u.toNode).trans ((congrArg Prod.fst he).trans hx.symm))
  have hY : E.nodeEmbedding v.toNode = y := Subtype.ext
    ((coupleContextNode_val D hS p v.toNode).trans ((congrArg Prod.snd he).trans hy.symm))
  have h := labels_eq_of_coupleCodePair (nativeCoupleGarden_decodes D hS p)
    (fun a => η (E.nodeEmbedding a)) (glued_couple_isDecoration D hS κ ρ p).2 r hr u v rfl rfl
  exact (congrArg η hX).symm.trans (h.trans (congrArg η hY))

theorem glueRelativeLabels_chain_edge {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (κ : GNode S.tree → (Fin d → ℤ))
    (ρ : (s : ReplacementSlot S) → NativeRelativeDecoration D hS d s) (b : GBranch S.tree)
    (q : Pair w) (hq : q ∈ (D.tree b).pairsAt (nodeSign S.sig b.1)
      (inflatedPosition S D.tree b.toNode))
    (x y : GNode (D.forest hS)) (hx : x.1 = q.1) (hy : y.1 = q.2) :
    glueRelativeLabels D hS κ ρ x = glueRelativeLabels D hS κ ρ y := by
  let a := inflatedPosition S D.tree b.toNode
  let f : Address 1 → Address w := fun z => addrExt a z.2
  have hmap : (D.tree b).pairsAt (nodeSign S.sig b.1) a =
      ((D.tree b).pairsAt (nodeSign S.sig b.1) ((0 : Fin 1),[])).map (fun z => (f z.1,f z.2)) := by
    have hh := chain_pairsAt_map (D.tree b) f (by intro z r; simp [f,addrExt,List.append_assoc])
      (nodeSign S.sig b.1) (0,[])
    simpa only [f,addrExt,List.append_nil] using hh
  rw [hmap] at hq
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hq
  let H := decodedTree (D.tree b) (nodeSign S.sig b.1)
  let η := glueRelativeLabels D hS κ ρ
  let u : GLeaf H.tree := ⟨r.1,(decodedTree_pairs_valid (D.tree b) (nodeSign S.sig b.1) r hr).1⟩
  let v : GLeaf H.tree := ⟨r.2,(decodedTree_pairs_valid (D.tree b) (nodeSign S.sig b.1) r hr).2⟩
  have hX : chainContextNode D hS b u.toNode = x := Subtype.ext ((congrArg Prod.fst he).trans hx.symm)
  have hY : chainContextNode D hS b v.toNode = y := Subtype.ext ((congrArg Prod.snd he).trans hy.symm)
  have h := labels_eq_of_chainCodePair (decodedTree_decodes _ _)
    (fun a => η (chainContextNode D hS b a)) (glued_chain_isDecoration D hS κ ρ b).2 r hr u v rfl rfl
  exact (congrArg η hX).symm.trans (h.trans (congrArg η hY))

end WaveTurbulence.RegRed
