/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainSideBLifts

/-! # Separating the inner and rest chains from side-couple blocks -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- A rest-chain node is separated from any physical side-root pair. -/
theorem chain_rest_side_incomp {w : ℕ} (k : MiniTreeCode) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (j l : Fin 3) (hj : j ≠ k.c) (hl : l ≠ k.lone)
    (ht : target ∈ chainNodes s (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)) :
    IncompAddr target (addrExt a [j]) ∧ IncompAddr target (backRoot a k i l) := by
  have hb := chainNodes_below s _ _ _ ht
  have h := chain_side_rest_incomp k i a j l hj hl
  exact ⟨h.1.symm.descendants hb ⟨rfl,List.prefix_refl _⟩,
    h.2.symm.descendants hb ⟨rfl,List.prefix_refl _⟩⟩

/-- Orientation only swaps the two separation statements. -/
theorem incomp_orientedFrame {w : ℕ} (ε : ℤˣ) (target front back : Fin w × Path)
    (h : IncompAddr target front ∧ IncompAddr target back) :
    IncompAddr target (orientedFrame ε front back).1 ∧
      IncompAddr target (orientedFrame ε front back).2 := by
  by_cases he : ε = 1 <;> simp only [orientedFrame,he,ite_true,ite_false]
  · exact h
  · exact ⟨h.2,h.1⟩

/-- A rest-chain node is below the inner chain's unfilled hole. -/
theorem chain_rest_below_inner_hole {w : ℕ} (k : MiniTreeCode) (i s : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path)
    (ht : target ∈ chainNodes s (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone)) :
    Below (addrExt (addrExt a [k.c]) i.lonePath) target := by
  rw [← secondRoot_as_hole]
  apply below_trans _ (chainNodes_below s _ _ _ ht)
  rw [backRoot_eq]
  exact below_extend _ _

/-- An inner-chain node cannot be below the lower node of the outer pair. -/
theorem chain_inner_not_below_second {w : ℕ} (k : MiniTreeCode) (i : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path)
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c])) :
    ¬ Below (secondRoot a k i) target := by
  rw [secondRoot_as_hole]
  exact chainNodes_not_below_lone i _ _ _ ht

/-- Inner-chain insertion never visits a back child of its hole. -/
theorem chain_inner_not_in_back {w : ℕ} (k : MiniTreeCode) (i : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (j : Fin 3)
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c])) :
    ¬ Below (backRoot a k i j) target := by
  intro hb
  apply chain_inner_not_below_second k i ζ a target ht
  apply below_trans _ hb
  rw [backRoot_eq]
  exact below_extend _ _

/-- Inner-chain insertion is incomparable with every noncontinuation front slot. -/
theorem chain_inner_front_incomp {w : ℕ} (k : MiniTreeCode) (i : RegChain)
    (ζ : ℤˣ) (a target : Fin w × Path) (j : Fin 3) (hj : j ≠ k.c)
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c])) :
    IncompAddr target (addrExt a [j]) :=
  (incomp_distinct_children a k.c j [] [] hj.symm).descendants
    (chainNodes_below i _ _ _ ht) ⟨rfl,List.prefix_refl _⟩

/-- Neither root of a physical side couple contains a represented inner-chain node. -/
theorem chain_inner_side_not_mem (k : MiniTreeCode) (i : RegChain) (Q : RegCpl)
    (ζ ε : ℤˣ) (a target : Fin 2 × Path) (j l : Fin 3) (hj : j ≠ k.c)
    (ht : target ∈ chainNodes i (slotSign ζ k.c) (addrExt a [k.c])) :
    target ∉ coupleNodes Q (orientedFrame ε (addrExt a [j]) (backRoot a k i l)).1
      (orientedFrame ε (addrExt a [j]) (backRoot a k i l)).2 := by
  intro hm
  rcases orientedFrame_node_below Q ε _ _ target hm with hf | hb
  · exact (chain_inner_front_incomp k i ζ a target j hj ht).2 hf
  · exact chain_inner_not_in_back k i ζ a target l ht hb

end WaveTurbulence.Reg
