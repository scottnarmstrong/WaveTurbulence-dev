/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainLowerExternal

/-! # Every represented chain follows the actual unique-L-child spine -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The chain's literal lone path is a unique-L-child segment of the actual carrier.
All local closure and extraction data are supplied by the actual code blocks. -/
theorem chain_externalSegment (X : RegChain) (Q : RegCpl) (G : Garden 2) (hG : Q.Decodes G)
    (a : Fin 2 × Path) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some (X.plug ζ h))
    (hP : ∀ p ∈ X.pairsAt ζ a, p ∈ Q.raw.2)
    (hL : ExternalAt G (addrExt a X.lonePath)) : ExternalSegment G a X.lonePath := by
  cases X with
  | nil => trivial
  | pair k r g i s =>
    have hfirst : UniqueExternalChild G a k.c := chain_child_external_iff Q G hG a k r g i s ζ h ha hP hL
    have hsecond : UniqueExternalChild G (secondRoot a k i) k.lone :=
      chain_lower_child_external_iff Q G hG a k r g i s ζ h ha hP hL
    have haI : Comb.subtree (G.tree (addrExt a [k.c]).1) (addrExt a [k.c]).2 =
        some (i.plug (slotSign ζ k.c) (chainLowerTree k r g s ζ h)) := by
      rw [subtree_addrExt G.tree a _ ha,chain_inner_subtree]
    have haS : Comb.subtree (G.tree (backRoot a k i k.lone).1) (backRoot a k i k.lone).2 =
        some (s.plug (slotSign (slotSign ζ k.c) k.lone) h) := by
      rw [subtree_addrExt G.tree a _ ha,chain_rest_subtree]
    have hLI : ExternalAt G (addrExt (addrExt a [k.c]) i.lonePath) := by
      rw [← secondRoot_as_hole]
      apply hL.ancestor
      have he : addrExt a (RegChain.pair k r g i s).lonePath =
          addrExt (secondRoot a k i) ([k.lone] ++ s.lonePath) := by
        simp only [RegChain.lonePath,secondRoot,addrExt_append,List.append_assoc]
      rw [he]
      exact below_extend _ _
    have hLS : ExternalAt G (addrExt (backRoot a k i k.lone) s.lonePath) := by
      rw [← chain_hole_as_rest a k r g i s]
      exact hL
    have hi := chain_externalSegment i Q G hG (addrExt a [k.c]) (slotSign ζ k.c)
      (chainLowerTree k r g s ζ h) haI
      (fun p hp => hP p (chain_inner_pair_inclusion k r g i s ζ a p hp)) hLI
    have hs := chain_externalSegment s Q G hG (backRoot a k i k.lone) (slotSign (slotSign ζ k.c) k.lone)
      h haS (fun p hp => hP p (chain_rest_pair_inclusion k r g i s ζ a p hp)) hLS
    have htail : ExternalSegment G (secondRoot a k i) ([k.lone] ++ s.lonePath) := by
      change UniqueExternalChild G (secondRoot a k i) k.lone ∧
        ExternalSegment G (addrExt (secondRoot a k i) [k.lone]) s.lonePath
      rw [← backRoot_eq]
      exact ⟨hsecond,hs⟩
    have hinner : ExternalSegment G (addrExt a [k.c]) (i.lonePath ++ ([k.lone] ++ s.lonePath)) := by
      apply (externalSegment_append G _ _ _).mpr
      rw [← secondRoot_as_hole]
      exact ⟨hi,htail⟩
    rw [RegChain.lonePath,List.append_assoc,List.append_assoc]
    exact ⟨hfirst,hinner⟩
termination_by structural X

end WaveTurbulence.Reg
