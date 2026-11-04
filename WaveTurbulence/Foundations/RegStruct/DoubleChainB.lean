/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DoubleChainPairLists

/-! # Actual source B on either side of a double-chain template -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Insertion on the positive side retains the full source double-chain pair list. -/
theorem doubleChain_positive_Bpairs (p n : RegChain) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes p 1 (0,[]) ∨ target = addrExt (0,[]) p.lonePath) :
    (joinChains (insertChainMini p 1 (0,[]) target m) n .triv).raw.2.Perm
      ((joinChains p n .triv).raw.opB target m).2 := by
  have hf := insertChainMini_pairs p ![1,-1] 1 (0,[]) target m nodeSign_root_zero ht
  have hb := chain_position_below p 1 (0,[]) target ht
  have hi : IncompAddr target ((1 : Fin 2),[]) :=
    ⟨fun h => (by decide : (1 : Fin 2) ≠ 0) (h.1.trans hb.1),
      fun h => (by decide : (1 : Fin 2) ≠ 0) (h.1.symm.trans hb.1)⟩
  have hn := relocate_chain_pairs_fixed n (-1) (1,[]) target m hi
  have hother : RawCpl.relocate target m.c m.lone (1,n.lonePath) = (1,n.lonePath) := by
    apply relocate_eq_of_not_below
    intro h
    exact (by decide : (1 : Fin 2) ≠ 0) (h.1.trans hb.1)
  have hhole : ((0 : Fin 2),(insertChainMini p 1 (0,[]) target m).lonePath) =
      RawCpl.relocate target m.c m.lone (0,p.lonePath) := by
    simpa only [addrExt,List.nil_append] using hf.2
  rw [doubleChain_pairs,raw_opB_pairs,doubleChain_pairs,List.map_append,List.map_append,List.map_singleton,
    hn,hother,← hhole]
  exact perm_lift_first _ _ (n.pairsAt (-1) (1,[]))
    [(((0 : Fin 2),(insertChainMini p 1 (0,[]) target m).lonePath),(1,n.lonePath))] _ hf.1

/-- The negative-side insertion has the same literal source fidelity. -/
theorem doubleChain_negative_Bpairs (p n : RegChain) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes n (-1) (1,[]) ∨ target = addrExt (1,[]) n.lonePath) :
    (joinChains p (insertChainMini n (-1) (1,[]) target m) .triv).raw.2.Perm
      ((joinChains p n .triv).raw.opB target m).2 := by
  have hf := insertChainMini_pairs n ![1,-1] (-1) (1,[]) target m nodeSign_root_one ht
  have hb := chain_position_below n (-1) (1,[]) target ht
  have hi : IncompAddr target ((0 : Fin 2),[]) :=
    ⟨fun h => (by decide : (0 : Fin 2) ≠ 1) (h.1.trans hb.1),
      fun h => (by decide : (0 : Fin 2) ≠ 1) (h.1.symm.trans hb.1)⟩
  have hp := relocate_chain_pairs_fixed p 1 (0,[]) target m hi
  have hother : RawCpl.relocate target m.c m.lone (0,p.lonePath) = (0,p.lonePath) := by
    apply relocate_eq_of_not_below
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (h.1.trans hb.1)
  have hhole : ((1 : Fin 2),(insertChainMini n (-1) (1,[]) target m).lonePath) =
      RawCpl.relocate target m.c m.lone (1,n.lonePath) := by
    simpa only [addrExt,List.nil_append] using hf.2
  rw [doubleChain_pairs,raw_opB_pairs,doubleChain_pairs,List.map_append,List.map_append,List.map_singleton,
    hp,hother,← hhole]
  exact perm_lift_middle (p.pairsAt 1 (0,[])) _ _
    [(((0 : Fin 2),p.lonePath),(1,(insertChainMini n (-1) (1,[]) target m).lonePath))] _ hf.1

/-- Actual B at a positive-chain position decodes to the new double chain. -/
theorem operationB_doubleChain_positive (p n : RegChain) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes p 1 (0,[]) ∨ target = addrExt (0,[]) p.lonePath) :
    decodedCouple (operationB (joinChains p n .triv) target m) =
      decodedCouple (joinChains (insertChainMini p 1 (0,[]) target m) n .triv) :=
  decodedCouple_eq_of_rawPairs_perm _ _
    ((operationB_pairs_perm _ target m (doubleChain_positive_position p n target ht)).trans
      (doubleChain_positive_Bpairs p n target m ht).symm)

/-- Actual B at a negative-chain position decodes to the new double chain. -/
theorem operationB_doubleChain_negative (p n : RegChain) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ chainNodes n (-1) (1,[]) ∨ target = addrExt (1,[]) n.lonePath) :
    decodedCouple (operationB (joinChains p n .triv) target m) =
      decodedCouple (joinChains p (insertChainMini n (-1) (1,[]) target m) .triv) :=
  decodedCouple_eq_of_rawPairs_perm _ _
    ((operationB_pairs_perm _ target m (doubleChain_negative_position p n target ht)).trans
      (doubleChain_negative_Bpairs p n target m ht).symm)

end WaveTurbulence.Reg
