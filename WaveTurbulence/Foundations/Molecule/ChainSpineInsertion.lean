/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ReverseRange

/-! # B insertion along the actual lone-leaf spine preserves bare chains -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Concatenating two bare chain contexts retains bare source data. -/
theorem appendChain_bare (X Y : RegChain) (hX : BareChain X) (hY : BareChain Y) : BareChain (appendChain X Y) := by
  cases X with
  | nil => exact hY
  | pair k r g i s =>
    obtain ⟨rfl,rfl,hi,hs⟩ := hX
    exact ⟨rfl,rfl,hi,appendChain_bare s Y hs hY⟩
termination_by structural X

/-- A side-couple node cannot be an ancestor of the whole chain's lone slot. -/
theorem chain_red_node_not_above_hole (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin 2 × Path)
    (ht : target ∈ coupleNodes r (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2) :
    ¬ Below target (addrExt a (RegChain.pair k r g i s).lonePath) := by
  have hi := (chain_red_node_separation k r i ζ a target ht).2.1
  rw [chain_hole_as_rest]
  exact not_below_extension hi.1 hi.2 s.lonePath

/-- The other side-couple block is likewise off the entire source spine. -/
theorem chain_green_node_not_above_hole (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin 2 × Path)
    (ht : target ∈ coupleNodes g (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2) :
    ¬ Below target (addrExt a (RegChain.pair k r g i s).lonePath) := by
  have hi := (chain_green_node_separation k g i ζ a target ht).2.1
  rw [chain_hole_as_rest]
  exact not_below_extension hi.1 hi.2 s.lonePath

/-- Every actual permitted insertion on the root-to-lone path retains a bare chain. -/
theorem insertChainMini_bare (X : RegChain) (hX : BareChain X) (ζ : ℤˣ)
    (a target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes X ζ a ∨ target = addrExt a X.lonePath)
    (hspine : Below target (addrExt a X.lonePath)) : BareChain (insertChainMini X ζ a target m) := by
  by_cases hh : target = addrExt a X.lonePath
  · rw [insertChainMini,ite_eq_left hh]
    exact appendChain_bare X (miniChain m) hX ⟨rfl,rfl,trivial,trivial⟩
  · rw [insertChainMini,ite_eq_right hh]
    have ht := ht.resolve_right hh
    cases X with
    | nil => simp [chainNodes] at ht
    | pair k r g i s =>
      obtain ⟨rfl,rfl,hi,hs⟩ := hX
      by_cases ha : target = a
      · subst target
        rw [insertMiniChain_at_root]
        exact ⟨rfl,rfl,trivial,⟨rfl,rfl,hi,hs⟩⟩
      by_cases hb : target = secondRoot a k i
      · subst target
        rw [insertMiniChain,ite_eq_right (secondRoot_ne a k i),ite_eq_left rfl]
        exact ⟨rfl,rfl,appendChain_bare i (miniChain m) hi ⟨rfl,rfl,trivial,trivial⟩,hs⟩
      simp only [chainNodes,sideNodes_eq_frame,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with (((hroot | hr) | hg) | hinner) | hrest
      · exact (hroot.elim ha hb).elim
      · exact (chain_red_node_not_above_hole k .triv .triv i s ζ a target hr hspine).elim
      · exact (chain_green_node_not_above_hole k .triv .triv i s ζ a target hg hspine).elim
      · have hsecondBelow : Below (secondRoot a k i) (addrExt a (RegChain.pair k .triv .triv i s).lonePath) := by
          rw [chain_hole_as_rest,backRoot_eq,addrExt_append]
          exact below_extend _ _
        have hspI := (below_comparable hspine hsecondBelow).resolve_right
          (chain_inner_not_below_second k i ζ a target hinner)
        rw [secondRoot_as_hole] at hspI
        have hbareI := insertChainMini_bare i hi (slotSign ζ k.c) (addrExt a [k.c]) target m (Or.inl hinner) hspI
        have hnot : target ≠ addrExt (addrExt a [k.c]) i.lonePath := by
          intro he
          apply chainNodes_no_lone i (slotSign ζ k.c) (addrExt a [k.c])
          rwa [← he]
        rw [insertChainMini,ite_eq_right hnot] at hbareI
        rw [insertMiniChain_inner k .triv .triv i s ζ a target m ha hb hinner]
        exact ⟨rfl,rfl,hbareI,hs⟩
      · have hspS : Below target (addrExt (backRoot a k i k.lone) s.lonePath) := by
          rw [← chain_hole_as_rest a k .triv .triv i s]
          exact hspine
        have hbareS := insertChainMini_bare s hs (slotSign (slotSign ζ k.c) k.lone)
          (backRoot a k i k.lone) target m (Or.inl hrest) hspS
        have hnot : target ≠ addrExt (backRoot a k i k.lone) s.lonePath := by
          intro he
          apply chainNodes_no_lone s (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)
          rwa [← he]
        rw [insertChainMini,ite_eq_right hnot] at hbareS
        rw [insertMiniChain_rest k .triv .triv i s ζ a target m ha hb hrest]
        exact ⟨rfl,rfl,hi,hbareS⟩
termination_by structural X

end WaveTurbulence.Reg
