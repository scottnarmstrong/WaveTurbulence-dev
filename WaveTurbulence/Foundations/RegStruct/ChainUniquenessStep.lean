/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeUniquenessInduction

/-! # The chain half of simultaneous uniqueness: the actual induction step -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Smaller-order couple and chain uniqueness prove the current chain case.
The final simultaneous induction supplies both hypotheses from strictly smaller orders. -/
theorem chain_unique_induction_step (N : ℕ)
    (ih : ∀ M < N, CoupleUniqueUpTo M ∧ ChainUniqueUpTo M) : ChainUniqueUpTo N := by
  intro X Y hN hwX hwY Q G hG a ζ h h' ha ha' hP hP' hpath
  cases X with
  | nil =>
    cases Y with
    | nil => rfl
    | pair k r g i s => simp [RegChain.lonePath] at hpath
  | pair k r g i s =>
    cases Y with
    | nil => simp [RegChain.lonePath] at hpath
    | pair l r' g' i' s' =>
      have haddr := chain_pair_addresses_unique Q G hG a k l r g r' g' i s i' s' ζ h h' ha ha' hP hP' hpath
      obtain ⟨hkl,hIL,hSL⟩ := haddr
      subst l
      have hside := chain_side_carriers_unique Q G a k r g r' g' i s i' s' ζ h h' ha ha' hP hP' hIL
      simp only [RegChain.wf,Bool.and_eq_true] at hwX hwY
      change r.size + g.size + i.size + s.size + 2 ≤ N at hN
      have hr := (ih r.size (by omega)).1 r r' le_rfl hwX.1.1.1 hwY.1.1.1 hside.1
      have hg := (ih g.size (by omega)).1 g g' le_rfl hwX.1.1.2 hwY.1.1.2 hside.2
      have haI : Comb.subtree (G.tree (addrExt a [k.c]).1) (addrExt a [k.c]).2 =
          some (i.plug (slotSign ζ k.c) (chainLowerTree k r g s ζ h)) := by
        rw [subtree_addrExt G.tree a _ ha,chain_inner_subtree]
      have haI' : Comb.subtree (G.tree (addrExt a [k.c]).1) (addrExt a [k.c]).2 =
          some (i'.plug (slotSign ζ k.c) (chainLowerTree k r' g' s' ζ h')) := by
        rw [subtree_addrExt G.tree a _ ha',chain_inner_subtree]
      have hi := (ih i.size (by omega)).2 i i' le_rfl hwX.1.2 hwY.1.2 Q G hG
        (addrExt a [k.c]) (slotSign ζ k.c) _ _ haI haI'
        (fun p hp => hP p (chain_inner_pair_inclusion k r g i s ζ a p hp))
        (fun p hp => hP' p (chain_inner_pair_inclusion k r' g' i' s' ζ a p hp)) hIL
      have haS : Comb.subtree (G.tree (backRoot a k i k.lone).1) (backRoot a k i k.lone).2 =
          some (s.plug (slotSign (slotSign ζ k.c) k.lone) h) := by
        rw [subtree_addrExt G.tree a _ ha,chain_rest_subtree]
      have haS' : Comb.subtree (G.tree (backRoot a k i k.lone).1) (backRoot a k i k.lone).2 =
          some (s'.plug (slotSign (slotSign ζ k.c) k.lone) h') := by
        have hh := subtree_addrExt G.tree a _ ha' ([k.c] ++ i'.lonePath ++ [k.lone])
        rw [chain_rest_subtree] at hh
        simpa only [backRoot,hIL] using hh
      have hpS' : ∀ p ∈ s'.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i k.lone),
          p ∈ Q.raw.2 := by
        intro p hp
        have hh : p ∈ s'.pairsAt (slotSign (slotSign ζ k.c) k.lone) (backRoot a k i' k.lone) := by
          simpa only [backRoot,hIL] using hp
        exact hP' p (chain_rest_pair_inclusion k r' g' i' s' ζ a p hh)
      have hs := (ih s.size (by omega)).2 s s' le_rfl hwX.2 hwY.2 Q G hG
        (backRoot a k i k.lone) (slotSign (slotSign ζ k.c) k.lone) h h' haS haS'
        (fun p hp => hP p (chain_rest_pair_inclusion k r g i s ζ a p hp)) hpS' hSL
      cases hr
      cases hg
      cases hi
      cases hs
      rfl

end WaveTurbulence.Reg
