/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainSpines

/-! # Exact number of decoded leaf pairs (DH21 Propositions 4.7–4.8) -/

public section
namespace WaveTurbulence.Reg
open TTree

mutual
/-- A decoded couple of order n has n+1 leaf pairs, without using any characterization. -/
theorem couple_pairsAt_length {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    (Q.pairsAt a b).length = Q.size + 1 := by
  cases Q with
  | triv => rfl
  | type1 c r g d =>
    simp only [RegCpl.pairsAt, List.length_append, couple_pairsAt_length r,
      couple_pairsAt_length g, couple_pairsAt_length d, RegCpl.size]
    omega
  | type2 p m q =>
    simp only [RegCpl.pairsAt, List.length_append, chain_pairsAt_length p,
      chain_pairsAt_length m, couple_pairsAt_length q, RegCpl.size]
    omega
termination_by structural Q

/-- A chain context of order n has n paired leaf pairs and its lone slot. -/
theorem chain_pairsAt_length {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (X.pairsAt ζ a).length = X.size := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    by_cases hr : slotSign ζ m.red.1 = 1 <;>
      by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp only [RegChain.pairsAt, hr, hg, ite_true, ite_false, List.length_append,
        couple_pairsAt_length r, couple_pairsAt_length g, chain_pairsAt_length i,
        chain_pairsAt_length s, RegChain.size] <;> omega
termination_by structural X
end

end WaveTurbulence.Reg
