/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainContinuationBLifts

/-! # Terminal-couple frames in a two-chain context -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Extending each of two incomparable roots preserves a valid couple frame. -/
theorem terminalFrame_incomp {w : ℕ} (p n : RegChain) (a b : Fin w × Path)
    (hab : IncompAddr a b) : IncompAddr (addrExt a p.lonePath) (addrExt b n.lonePath) :=
  hab.descendants (below_extend _ _) (below_extend _ _)

/-- Spine terminal roots keep their incoming signs. -/
theorem terminalFrame_signs (σ : Fin 2 → ℤˣ) (p n : RegChain) (a b : Fin 2 × Path)
    (ha : nodeSign σ a = 1) (hb : nodeSign σ b = -1) :
    nodeSign σ (addrExt a p.lonePath) = 1 ∧ nodeSign σ (addrExt b n.lonePath) = -1 := by
  rw [nodeSign_spine,nodeSign_spine,ha,hb]
  exact ⟨rfl,rfl⟩

/-- A node of a chain cannot belong to a couple rooted at its hole and a disjoint root. -/
theorem chain_node_not_in_terminal {w : ℕ} (X : RegChain) (Q : RegCpl) (ζ : ℤˣ)
    (a b target : Fin w × Path) (hab : IncompAddr a b)
    (ht : target ∈ chainNodes X ζ a) :
    target ∉ coupleNodes Q (addrExt a X.lonePath) b := by
  intro hm
  rcases coupleNodes_below Q _ _ _ hm with hh | hb
  · exact chainNodes_not_below_lone X ζ a target ht hh
  · exact (below_comparable (chainNodes_below X ζ a target ht) hb).elim hab.1 hab.2

/-- The same exclusion holds with the two terminal roots in reversed order. -/
theorem chain_node_not_in_terminal_swap {w : ℕ} (X : RegChain) (Q : RegCpl) (ζ : ℤˣ)
    (a b target : Fin w × Path) (hab : IncompAddr a b)
    (ht : target ∈ chainNodes X ζ a) :
    target ∉ coupleNodes Q b (addrExt a X.lonePath) := by
  intro hm
  rcases coupleNodes_below Q _ _ _ hm with hb | hh
  · exact (below_comparable (chainNodes_below X ζ a target ht) hb).elim hab.1 hab.2
  · exact chainNodes_not_below_lone X ζ a target ht hh

/-- A terminal-couple node cannot be represented by its enclosing left chain. -/
theorem terminal_node_not_in_chain {w : ℕ} (X : RegChain) (Q : RegCpl) (ζ : ℤˣ)
    (a b target : Fin w × Path) (hab : IncompAddr a b)
    (ht : target ∈ coupleNodes Q (addrExt a X.lonePath) b) :
    target ∉ chainNodes X ζ a := by
  intro hm
  exact chain_node_not_in_terminal X Q ζ a b target hab hm ht

/-- Inserting in a terminal couple leaves the enclosing left chain's pairs fixed. -/
theorem terminal_node_chain_pairs_fixed (X : RegChain) (Q : RegCpl) (ζ : ℤˣ)
    (a b target : Fin 2 × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ht : target ∈ coupleNodes Q (addrExt a X.lonePath) b) :
    (X.pairsAt ζ a).map (fun p =>
      (RawCpl.relocate target m.c m.lone p.1,RawCpl.relocate target m.c m.lone p.2)) = X.pairsAt ζ a := by
  rcases coupleNodes_below Q _ _ _ ht with hh | hb
  · exact relocate_pairs_below_chain_hole X ζ a target m.c m.lone hh
  · exact relocate_chain_pairs_fixed X ζ a target m
      ((hab.symm).descendants hb ⟨rfl,List.prefix_refl _⟩)

/-- Swapping roots does not change the terminal-node exclusion argument. -/
theorem terminal_node_not_in_chain_swap {w : ℕ} (X : RegChain) (Q : RegCpl) (ζ : ℤˣ)
    (a b target : Fin w × Path) (hab : IncompAddr a b)
    (ht : target ∈ coupleNodes Q b (addrExt a X.lonePath)) :
    target ∉ chainNodes X ζ a := by
  intro hm
  exact chain_node_not_in_terminal_swap X Q ζ a b target hab hm ht

/-- Terminal insertion also fixes the enclosing chain when its root is the negative frame root. -/
theorem terminal_node_chain_pairs_fixed_swap (X : RegChain) (Q : RegCpl) (ζ : ℤˣ)
    (a b target : Fin 2 × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ht : target ∈ coupleNodes Q b (addrExt a X.lonePath)) :
    (X.pairsAt ζ a).map (fun p =>
      (RawCpl.relocate target m.c m.lone p.1,RawCpl.relocate target m.c m.lone p.2)) = X.pairsAt ζ a := by
  rcases coupleNodes_below Q _ _ _ ht with hb | hh
  · exact relocate_chain_pairs_fixed X ζ a target m
      ((hab.symm).descendants hb ⟨rfl,List.prefix_refl _⟩)
  · exact relocate_pairs_below_chain_hole X ζ a target m.c m.lone hh

end WaveTurbulence.Reg
