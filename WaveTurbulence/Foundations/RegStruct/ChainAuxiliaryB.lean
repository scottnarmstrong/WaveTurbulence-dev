/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainMiniFidelity

/-! # Actual source B on a chain's auxiliary couple -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- In positive orientation, all old pairs and the terminal pair have exactly the source B image. -/
theorem treeAuxCode_positive_Bpairs (X : RegChain) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes X 1 (0,[]) ∨ target = addrExt (0,[]) X.lonePath) :
    (treeAuxCode (insertChainMini X 1 (0,[]) target m) 1).raw.2.Perm
      ((treeAuxCode X 1).raw.opB target m).2 := by
  have hf := insertChainMini_pairs X ![1,-1] 1 (0,[]) target m nodeSign_root_zero ht
  have hb := chain_position_below X 1 (0,[]) target ht
  have hother : RawCpl.relocate target m.c m.lone (1,[]) = (1,[]) := by
    apply relocate_eq_of_not_below
    intro hh
    exact (by decide : (1 : Fin 2) ≠ 0) (hh.1.trans hb.1)
  have hhole : ((0 : Fin 2),(insertChainMini X 1 (0,[]) target m).lonePath) =
      RawCpl.relocate target m.c m.lone (0,X.lonePath) := by
    simpa only [addrExt,List.nil_append] using hf.2
  rw [treeAuxCode_positive_pairs,raw_opB_pairs,treeAuxCode_positive_pairs,List.map_append,List.map_singleton,
    hother,← hhole]
  simpa only [List.append_nil] using perm_lift_first _ _
    [(((0 : Fin 2),(insertChainMini X 1 (0,[]) target m).lonePath),(1,[]))] [] _ hf.1

/-- The negative orientation has the same literal source fidelity. -/
theorem treeAuxCode_negative_Bpairs (X : RegChain) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes X (-1) (1,[]) ∨ target = addrExt (1,[]) X.lonePath) :
    (treeAuxCode (insertChainMini X (-1) (1,[]) target m) (-1)).raw.2.Perm
      ((treeAuxCode X (-1)).raw.opB target m).2 := by
  have hf := insertChainMini_pairs X ![1,-1] (-1) (1,[]) target m nodeSign_root_one ht
  have hb := chain_position_below X (-1) (1,[]) target ht
  have hother : RawCpl.relocate target m.c m.lone (0,[]) = (0,[]) := by
    apply relocate_eq_of_not_below
    intro hh
    exact (by decide : (0 : Fin 2) ≠ 1) (hh.1.trans hb.1)
  have hhole : ((1 : Fin 2),(insertChainMini X (-1) (1,[]) target m).lonePath) =
      RawCpl.relocate target m.c m.lone (1,X.lonePath) := by
    simpa only [addrExt,List.nil_append] using hf.2
  rw [treeAuxCode_negative_pairs,raw_opB_pairs,treeAuxCode_negative_pairs,List.map_append,List.map_singleton,
    hother,← hhole]
  simpa only [List.append_nil] using perm_lift_first _ _
    [(((0 : Fin 2),[]),(1,(insertChainMini X (-1) (1,[]) target m).lonePath))] [] _ hf.1

/-- At every permitted chain position, actual source B decodes to the inserted chain's auxiliary carrier. -/
theorem operationB_treeAux_carrier (X : RegChain) (ζ : ℤˣ) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes X ζ ((if ζ = 1 then 0 else 1),[]) ∨
      target = addrExt ((if ζ = 1 then 0 else 1),[]) X.lonePath) :
    decodedCouple (operationB (treeAuxCode X ζ) target m) =
      decodedCouple (treeAuxCode (insertChainMini X ζ ((if ζ = 1 then 0 else 1),[]) target m) ζ) := by
  have hn := treeAuxCode_position_node X ζ target ht
  have hp := operationB_pairs_perm (treeAuxCode X ζ) target m hn
  apply decodedCouple_eq_of_rawPairs_perm
  apply hp.trans
  by_cases hζ : ζ = 1
  · subst ζ
    exact (treeAuxCode_positive_Bpairs X target m ht).symm
  · have hm : ζ = -1 := (Int.units_eq_one_or _).resolve_left hζ
    subst ζ
    exact (treeAuxCode_negative_Bpairs X target m ht).symm

/-- Every bare chain auxiliary carrier is source regular, by actual permitted B insertions. -/
theorem bareChain_aux_isRegular (X : RegChain) (hX : BareChain X) (ζ : ℤˣ) :
    IsRegularCouple (decodedCouple (treeAuxCode X ζ)) := by
  generalize hs : X.size = N
  induction N using Nat.strong_induction_on generalizing X with
  | h N ih =>
    by_cases hnil : X = .nil
    · subst X
      have he : treeAuxCode .nil ζ = .triv := by
        by_cases hζ : ζ = 1 <;> simp [treeAuxCode,hζ,joinChains,RegChain.isNil]
      rw [he]
      exact decodedTriv_isRegular
    · obtain ⟨Y,m,target,hY,hsize,ht,he⟩ := bareChain_prune X hX hnil ζ ((if ζ = 1 then 0 else 1),[])
      have hregY := ih Y.size (by omega) Y hY rfl
      have hnode := treeAuxCode_position_node Y ζ target ht
      have hreg := isRegularCouple_operationB (treeAuxCode Y ζ) hregY target m hnode
      have hcarrier := operationB_treeAux_carrier Y ζ target m ht
      rw [he] at hcarrier
      rw [← hcarrier]
      exact hreg

end WaveTurbulence.Reg
