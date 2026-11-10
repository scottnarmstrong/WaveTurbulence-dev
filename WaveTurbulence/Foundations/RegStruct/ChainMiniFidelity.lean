/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.BareChainPruning
public import WaveTurbulence.Foundations.RegStruct.SourceCodeOperations

/-! # Exact B fidelity at represented chain nodes and at the source lone leaf -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The source-permitted lone-leaf B-step has the same pair/hole fidelity as an internal node step. -/
theorem insertChainMini_pairs (X : RegChain) (σ : Fin 2 → ℤˣ) (ζ : ℤˣ)
    (a target : Fin 2 × Path) (m : MiniTreeCode) (ha : nodeSign σ a = ζ)
    (ht : target ∈ chainNodes X ζ a ∨ target = addrExt a X.lonePath) :
    (((insertChainMini X ζ a target m).pairsAt ζ a).Perm
      ((X.pairsAt ζ a).map (fun p =>
        (RawCpl.relocate target m.c m.lone p.1,RawCpl.relocate target m.c m.lone p.2)) ++
        (miniChain m).pairsAt (nodeSign σ target) target)) ∧
      addrExt a (insertChainMini X ζ a target m).lonePath =
        RawCpl.relocate target m.c m.lone (addrExt a X.lonePath) := by
  by_cases he : target = addrExt a X.lonePath
  · subst target
    rw [insertChainMini,ite_eq_left rfl]
    constructor
    · rw [appendChain_pairsAt,relocate_pairs_below_chain_hole X ζ a _ m.c m.lone ⟨rfl,List.prefix_refl _⟩,
        nodeSign_spine,ha]
    · rw [appendChain_lonePath,miniChain_lonePath,relocate_self,addrExt_append]
  · rw [insertChainMini,ite_eq_right he]
    exact insertMiniChain_pairs X σ ζ a target m ha (ht.resolve_right he)

/-- A permitted chain insertion position is always below its actual original root. -/
theorem chain_position_below (X : RegChain) (ζ : ℤˣ) (a target : Fin 2 × Path)
    (ht : target ∈ chainNodes X ζ a ∨ target = addrExt a X.lonePath) : Below a target := by
  rcases ht with ht | rfl
  · exact chainNodes_below X ζ a target ht
  · exact below_extend _ _

end WaveTurbulence.Reg
