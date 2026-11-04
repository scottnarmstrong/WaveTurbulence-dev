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

/-- The auxiliary code's positive raw list, including its unique cross-tree terminal pair. -/
theorem treeAuxCode_positive_pairs (X : RegChain) :
    (treeAuxCode X 1).raw.2 = X.pairsAt 1 (0,[]) ++ [((0,X.lonePath),(1,[]))] := by
  cases X with
  | nil => simp [treeAuxCode,joinChains,RegChain.isNil,RegChain.pairsAt,RegChain.lonePath,RegCpl.raw,RegCpl.pairsAt]
  | pair k r g i s =>
    change ((RegChain.pair k r g i s).pairsAt 1 (0,[]) ++ [] ++ [((0,RegChain.lonePath (.pair k r g i s)),(1,[]))]) = _
    rw [List.append_nil]

/-- The auxiliary code's negative raw list, with the terminal pair oriented positive first. -/
theorem treeAuxCode_negative_pairs (X : RegChain) :
    (treeAuxCode X (-1)).raw.2 = X.pairsAt (-1) (1,[]) ++ [((0,[]),(1,X.lonePath))] := by
  cases X with
  | nil => simp [treeAuxCode,joinChains,RegChain.isNil,RegChain.pairsAt,RegChain.lonePath,RegCpl.raw,RegCpl.pairsAt]
  | pair k r g i s =>
    change ([] ++ (RegChain.pair k r g i s).pairsAt (-1) (1,[]) ++ [((0,[]),(1,RegChain.lonePath (.pair k r g i s)))]) = _
    rw [List.nil_append]

/-- Every permitted chain position is an actual node of its auxiliary couple. -/
theorem treeAuxCode_position_node (X : RegChain) (ζ : ℤˣ) (target : Fin 2 × Path)
    (ht : target ∈ chainNodes X ζ ((if ζ = 1 then 0 else 1),[]) ∨
      target = addrExt ((if ζ = 1 then 0 else 1),[]) X.lonePath) :
    target ∈ coupleNodes (treeAuxCode X ζ) (0,[]) (1,[]) := by
  by_cases hζ : ζ = 1
  · subst ζ
    cases X with
    | nil =>
      simp [chainNodes,RegChain.lonePath,addrExt,treeAuxCode,joinChains,RegChain.isNil,coupleNodes] at ht ⊢
      exact Or.inl ht
    | pair k r g i s =>
      change target ∈ (chainNodes (.pair k r g i s) 1 (0,[]) ∪ ∅) ∪ {addrExt (0,[]) (RegChain.pair k r g i s).lonePath,(1,[])}
      rcases ht with ht | ht
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ ht)
      · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl ht))
  · have hm : ζ = -1 := (Int.units_eq_one_or _).resolve_left hζ
    subst ζ
    cases X with
    | nil =>
      simp [chainNodes,RegChain.lonePath,addrExt,treeAuxCode,joinChains,RegChain.isNil,coupleNodes] at ht ⊢
      exact Or.inr ht
    | pair k r g i s =>
      change target ∈ (∅ ∪ chainNodes (.pair k r g i s) (-1) (1,[])) ∪ {(0,[]),addrExt (1,[]) (RegChain.pair k r g i s).lonePath}
      rcases ht with ht | ht
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ ht)
      · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr ht)))

end WaveTurbulence.Reg
