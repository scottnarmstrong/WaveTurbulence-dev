/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.LeafAddresses

/-! # Decoded pairs cover exactly the source leaves (DH21 Propositions 4.7–4.8)

These identities do not assume regularity or any unfinished characterization.
They retain literal global leaf addresses, including nested non-dominant chains.
-/

public section
namespace WaveTurbulence.Reg
open TTree Finset

mutual
/-- Every decoded couple pair endpoint is a leaf, and every leaf is a pair endpoint. -/
theorem couple_leafAddresses {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    leafAddresses Q.trees.1 a ∪ leafAddresses Q.trees.2 b = pairEndpoints (Q.pairsAt a b) := by
  cases Q with
  | triv => simp [RegCpl.trees, RegCpl.pairsAt]
  | type1 c r g d =>
    rw [RegCpl.pairsAt, pairEndpoints_append, pairEndpoints_append,
      ← couple_leafAddresses r, ← couple_leafAddresses g, ← couple_leafAddresses d]
    fin_cases c <;>
      simp [RegCpl.trees, MiniCplCode.partner, leafAddresses_node] <;> ac_rfl
  | type2 p m q =>
    rw [RegCpl.trees, chain_leafAddresses p, chain_leafAddresses m, RegCpl.pairsAt,
      pairEndpoints_append, pairEndpoints_append, ← couple_leafAddresses q]
    ac_rfl
termination_by structural Q

/-- A decoded chain's pairs cover all leaves except the subtree filled at its lone position. -/
theorem chain_leafAddresses {w : ℕ} (X : RegChain) (ζ : ℤˣ) (h : TTree) (a : Fin w × Path) :
    leafAddresses (X.plug ζ h) a =
      pairEndpoints (X.pairsAt ζ a) ∪ leafAddresses h (addrExt a X.lonePath) := by
  cases X with
  | nil => simp [RegChain.plug, RegChain.pairsAt, RegChain.lonePath, addrExt]
  | pair m r g i s =>
    have hr :=
      (couple_leafAddresses r
        (if slotSign ζ m.red.1 = 1 then addrExt a [m.red.1]
         else addrExt a ([m.c] ++ i.lonePath ++ [m.red.2]))
        (if slotSign ζ m.red.1 = 1 then addrExt a ([m.c] ++ i.lonePath ++ [m.red.2])
         else addrExt a [m.red.1]))
    have hg :=
      (couple_leafAddresses g
        (if slotSign ζ m.green.1 = 1 then addrExt a [m.green.1]
         else addrExt a ([m.c] ++ i.lonePath ++ [m.green.2]))
        (if slotSign ζ m.green.1 = 1 then addrExt a ([m.c] ++ i.lonePath ++ [m.green.2])
         else addrExt a [m.green.1]))
    obtain ⟨c,b⟩ := m
    rcases Int.units_eq_one_or ζ with hz | hz <;> subst ζ
    all_goals
      fin_cases c <;> fin_cases b
      all_goals
        simp [MiniTreeCode.red, MiniTreeCode.green, slotSign] at hr hg
        simp [RegChain.plug, RegChain.pairsAt, RegChain.lonePath, node3,
          MiniTreeCode.lone, MiniTreeCode.red, MiniTreeCode.green,
          slotSign, treeOfSign, leafAddresses_node, chain_leafAddresses i,
          chain_leafAddresses s, pairEndpoints_append, ← hr, ← hg, addrExt_append, List.append_assoc]
        ac_rfl
termination_by structural X
end

end WaveTurbulence.Reg
