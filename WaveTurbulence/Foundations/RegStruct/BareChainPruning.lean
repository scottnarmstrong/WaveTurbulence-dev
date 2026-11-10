/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainExternalSegments

/-! # Adjacent-pair pruning of actual bare chain codes -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- B insertion in a saturated chain, including its permitted lone-leaf position. -/
def insertChainMini (X : RegChain) (ζ : ℤˣ) (a target : Fin 2 × Path) (m : MiniTreeCode) : RegChain :=
  if target = addrExt a X.lonePath then appendChain X (miniChain m)
  else insertMiniChain X ζ a target m

/-- A nonempty chain represents its first branching node. -/
theorem chain_root_mem (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (a : Fin 2 × Path) :
    a ∈ chainNodes (.pair k r g i s) ζ a := by
  simp only [chainNodes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl trivial))))

/-- Insertion at the first position always prepends its adjacent pair of spine nodes. -/
theorem insertChainMini_root (X : RegChain) (ζ : ℤˣ) (a : Fin 2 × Path) (m : MiniTreeCode) :
    insertChainMini X ζ a a m = .pair m .triv .triv .nil X := by
  cases X with
  | nil => simp [insertChainMini,RegChain.lonePath,addrExt,appendChain,miniChain]
  | pair k r g i s =>
    have hn : a ≠ addrExt a (RegChain.pair k r g i s).lonePath := by
      intro he
      apply chainNodes_no_lone (.pair k r g i s) ζ a
      rw [← he]
      exact chain_root_mem k r g i s ζ a
    rw [insertChainMini,ite_eq_right hn,insertMiniChain_at_root]

/-- Every nonempty bare chain is obtained from a smaller bare chain by one permitted B-step.
This is the constructive adjacent-insertion form of the chain grammar. -/
theorem bareChain_prune (X : RegChain) (hX : BareChain X) (hne : X ≠ .nil)
    (ζ : ℤˣ) (a : Fin 2 × Path) :
    ∃ (Y : RegChain) (m : MiniTreeCode) (target : Fin 2 × Path),
      BareChain Y ∧ Y.size+2 = X.size ∧
      (target ∈ chainNodes Y ζ a ∨ target = addrExt a Y.lonePath) ∧ insertChainMini Y ζ a target m = X := by
  cases X with
  | nil => exact (hne rfl).elim
  | pair k r g i s =>
    obtain ⟨rfl,rfl,hi,hs⟩ := hX
    cases i with
    | nil =>
      refine ⟨s,k,a,hs,?_,?_,insertChainMini_root s ζ a k⟩
      · simp only [RegChain.size,RegCpl.size,Nat.zero_add,Nat.add_zero]
      · cases s with
        | nil => exact Or.inr (by simp [RegChain.lonePath,addrExt])
        | pair l r g j t => exact Or.inl (chain_root_mem l r g j t ζ a)
    | pair l r g j t =>
      obtain ⟨Y,m,target,hY,hsize,htarget,hinsert⟩ := bareChain_prune (.pair l r g j t) hi (by simp) (slotSign ζ k.c) (addrExt a [k.c])
      let Z := RegChain.pair k .triv .triv Y s
      have htZ : target ∈ chainNodes Z ζ a := by
        rcases htarget with ht | ht
        · simp only [Z,chainNodes,Finset.mem_union]
          exact Or.inl (Or.inr ht)
        · have he : target = secondRoot a k Y := by rw [secondRoot_as_hole]; exact ht
          simp only [Z,chainNodes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
          exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr he))))
      have htHole : target ≠ addrExt a Z.lonePath := by
        intro he
        rw [he] at htZ
        exact chainNodes_no_lone Z ζ a htZ
      refine ⟨Z,m,target,⟨rfl,rfl,hY,hs⟩,?_,Or.inl htZ,?_⟩
      · simp only [Z,RegChain.size,RegCpl.size,Nat.zero_add]
        simp only [RegChain.size] at hsize
        omega
      · rw [insertChainMini,ite_eq_right htHole]
        rcases htarget with ht | ht
        · have htI : target ≠ addrExt (addrExt a [k.c]) Y.lonePath := by
            intro he
            rw [he] at ht
            exact chainNodes_no_lone Y _ _ ht
          rw [insertChainMini,ite_eq_right htI] at hinsert
          have hroot : target ≠ a := below_child_ne_root a target k.c [] (chainNodes_below Y _ _ _ ht)
          have hlower : target ≠ secondRoot a k Y := by
            intro he
            apply htI
            rw [he,secondRoot_as_hole]
          rw [insertMiniChain_inner k .triv .triv Y s ζ a target m hroot hlower ht,hinsert]
        · have he : target = secondRoot a k Y := by rw [secondRoot_as_hole]; exact ht
          rw [insertChainMini,ite_eq_left ht] at hinsert
          change insertMiniChain (.pair k .triv .triv Y s) ζ a target m = _
          rw [he,insertMiniChain,ite_eq_right (secondRoot_ne a k Y),ite_eq_left rfl,hinsert]
termination_by structural X

end WaveTurbulence.Reg
