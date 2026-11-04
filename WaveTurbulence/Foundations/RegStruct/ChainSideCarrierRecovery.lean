/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainPairAddressRecovery

/-! # Recovering the actual red and green child carriers of a chain pair -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Shared actual extractions and ambient pair blocks identify the decoded child carrier. -/
theorem decodedCouple_eq_of_actual_block (Q C D : RegCpl) (G : Garden 2)
    (a b : Fin 2 × Path) (hab : IncompAddr a b)
    (ha : Comb.subtree (G.tree a.1) a.2 = some C.trees.1)
    (hb : Comb.subtree (G.tree b.1) b.2 = some C.trees.2)
    (ha' : Comb.subtree (G.tree a.1) a.2 = some D.trees.1)
    (hb' : Comb.subtree (G.tree b.1) b.2 = some D.trees.2)
    (hC : ∀ p ∈ C.pairsAt a b, p ∈ Q.raw.2)
    (hD : ∀ p ∈ D.pairsAt a b, p ∈ Q.raw.2) : decodedCouple C = decodedCouple D := by
  have ht : C.trees = D.trees := Prod.ext (Option.some.inj (ha.symm.trans ha'))
    (Option.some.inj (hb.symm.trans hb'))
  exact decodedCouple_eq_of_common_frame Q C D a b hab ht
    (symmPairs_subset_of_pairs_subset hC) (symmPairs_subset_of_pairs_subset hD)

/-- Recovered chain-pair positions determine both actual side-couple carriers. -/
theorem chain_side_carriers_unique (Q : RegCpl) (G : Garden 2)
    (a : Fin 2 × Path) (k : MiniTreeCode) (r g r' g' : RegCpl) (i s i' s' : RegChain)
    (ζ : ℤˣ) (h h' : TTree)
    (ha : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h))
    (ha' : Comb.subtree (G.tree a.1) a.2 = some ((RegChain.pair k r' g' i' s').plug ζ h'))
    (hP : ∀ p ∈ (RegChain.pair k r g i s).pairsAt ζ a, p ∈ Q.raw.2)
    (hP' : ∀ p ∈ (RegChain.pair k r' g' i' s').pairsAt ζ a, p ∈ Q.raw.2)
    (hi : i.lonePath = i'.lonePath) :
    decodedCouple r = decodedCouple r' ∧ decodedCouple g = decodedCouple g' := by
  constructor
  · have hc := chain_red_frame_extraction G.tree a k r g i s ζ h ha
    have hd := chain_red_frame_extraction G.tree a k r' g' i' s' ζ h' ha'
    have hd' :
        Comb.subtree (G.tree (chainRedFrame k i ζ a).1.1) (chainRedFrame k i ζ a).1.2 = some r'.trees.1 ∧
        Comb.subtree (G.tree (chainRedFrame k i ζ a).2.1) (chainRedFrame k i ζ a).2.2 = some r'.trees.2 := by
      simpa only [chainRedFrame,backRoot,hi] using hd
    apply decodedCouple_eq_of_actual_block Q r r' G _ _ (chainRedFrame_incomp k i ζ a) hc.1 hc.2 hd'.1 hd'.2
    · exact fun p hp => hP p (chain_red_pair_inclusion k r g i s ζ a p hp)
    · intro p hp
      have hp' : p ∈ r'.pairsAt (chainRedFrame k i' ζ a).1 (chainRedFrame k i' ζ a).2 := by
        simpa only [chainRedFrame,backRoot,hi] using hp
      exact hP' p (chain_red_pair_inclusion k r' g' i' s' ζ a p hp')
  · have hc := chain_green_frame_extraction G.tree a k r g i s ζ h ha
    have hd := chain_green_frame_extraction G.tree a k r' g' i' s' ζ h' ha'
    have hd' :
        Comb.subtree (G.tree (chainGreenFrame k i ζ a).1.1) (chainGreenFrame k i ζ a).1.2 = some g'.trees.1 ∧
        Comb.subtree (G.tree (chainGreenFrame k i ζ a).2.1) (chainGreenFrame k i ζ a).2.2 = some g'.trees.2 := by
      simpa only [chainGreenFrame,backRoot,hi] using hd
    apply decodedCouple_eq_of_actual_block Q g g' G _ _ (chainGreenFrame_incomp k i ζ a) hc.1 hc.2 hd'.1 hd'.2
    · exact fun p hp => hP p (chain_green_pair_inclusion k r g i s ζ a p hp)
    · intro p hp
      have hp' : p ∈ g'.pairsAt (chainGreenFrame k i' ζ a).1 (chainGreenFrame k i' ζ a).2 := by
        simpa only [chainGreenFrame,backRoot,hi] using hp
      exact hP' p (chain_green_pair_inclusion k r' g' i' s' ζ a p hp')

end WaveTurbulence.Reg
