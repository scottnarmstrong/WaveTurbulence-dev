/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OperationBPairFidelity

/-! # Normalized operation B at every actual node -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- The literal source B pair list is its relocation followed by the mini-tree pairs. -/
theorem raw_opB_pairs (R : RawCpl) (target : Fin 2 × Path) (m : MiniTreeCode) :
    (R.opB target m).2 = R.2.map (fun x =>
      (RawCpl.relocate target m.c m.lone x.1,RawCpl.relocate target m.c m.lone x.2)) ++
      (miniChain m).pairsAt (nodeSign ![1,-1] target) target := by
  simp only [RawCpl.opB,miniChain_pairsAt]

/-- At any actual node, normalized code B has exactly the source pair list up to order. -/
theorem operationB_pairs_perm (Q : RegCpl) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ coupleNodes Q (0,[]) (1,[])) :
    (operationB Q target m).raw.2.Perm (Q.raw.opB target m).2 := by
  apply (normalizeCouple_pairs_perm _).trans
  rw [raw_opB_pairs]
  exact insertMiniCouple_pairs Q ![1,-1] (0,[]) (1,[]) target m
    ⟨(by intro h; exact (by decide : (1 : Fin 2) ≠ 0) h.1),
      (by intro h; exact (by decide : (0 : Fin 2) ≠ 1) h.1)⟩
    nodeSign_root_zero nodeSign_root_one ht

/-- Every actual node insertion adds two branching nodes to the normalized code. -/
theorem operationB_size (Q : RegCpl) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ coupleNodes Q (0,[]) (1,[])) :
    (operationB Q target m).size = Q.size + 2 := by
  have hl := (operationB_pairs_perm Q target m ht).length_eq
  rw [raw_opB_pairs_length] at hl
  change ((operationB Q target m).pairsAt (0,[]) (1,[])).length =
    (Q.pairsAt (0,[]) (1,[])).length + 2 at hl
  rw [couple_pairsAt_length,couple_pairsAt_length] at hl
  omega

end WaveTurbulence.Reg
