/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.RelocationGeometry
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.Type2BLifts
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.BContext.Type1BLifts


/-! # Pair-list fidelity of operation B at every represented node

The mutual proof consumes actual node membership. Each local permutation is
produced recursively on a child code, then lifted through its constructor.
-/

public section
namespace WaveTurbulence.Reg.Skeleton.BContext
open TTree
variable {w : ℕ}

/-- The sign-oriented frame really has signs positive and negative. -/
theorem orientedFrame_signs (σ : Fin w → ℤˣ) (ε : ℤˣ) (front back : Fin w × Path)
    (hf : nodeSign σ front = ε) (hb : nodeSign σ back = -ε) :
    nodeSign σ (orientedFrame ε front back).1 = 1 ∧
      nodeSign σ (orientedFrame ε front back).2 = -1 := by
  by_cases he : ε = 1
  · simp only [orientedFrame,he,ite_true]
    exact ⟨hf.trans he,hb.trans (congrArg Neg.neg he)⟩
  · have hm : ε = -1 := (Int.units_eq_one_or ε).resolve_left he
    simp only [orientedFrame,he,ite_false]
    constructor
    · rw [hb,hm,neg_neg]
    · exact hf.trans hm

/-- The sign data required to recurse into the red side couple. -/
theorem chainRedFrame_signs (σ : Fin w → ℤˣ) (k : MiniTreeCode) (i : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (ha : nodeSign σ a = ζ) :
    nodeSign σ (chainRedFrame k i ζ a).1 = 1 ∧ nodeSign σ (chainRedFrame k i ζ a).2 = -1 := by
  apply orientedFrame_signs
  · rw [nodeSign_step,ha]
  · rw [nodeSign_chain_child,ha,slotSign_red]

/-- The sign data required to recurse into the green side couple. -/
theorem chainGreenFrame_signs (σ : Fin w → ℤˣ) (k : MiniTreeCode) (i : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (ha : nodeSign σ a = ζ) :
    nodeSign σ (chainGreenFrame k i ζ a).1 = 1 ∧ nodeSign σ (chainGreenFrame k i ζ a).2 = -1 := by
  apply orientedFrame_signs
  · rw [nodeSign_step,ha]
  · rw [nodeSign_chain_child,ha,slotSign_green]


mutual
/-- Code insertion implements the literal source relocation and two new pairs. -/
theorem insertMiniCouple_pairs (Q : RegCpl) (σ : Fin w → ℤˣ)
    (a b target : Fin w × Path) (m : MiniTreeCode) (hab : IncompAddr a b)
    (ha : nodeSign σ a = 1) (hb : nodeSign σ b = -1)
    (ht : target ∈ coupleNodes Q a b) :
    ((insertMiniCouple Q a b target m).pairsAt a b).Perm
      ((Q.pairsAt a b).map (fun x =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone x.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone x.2)) ++
        (miniChain m).pairsAt (nodeSign σ target) target) := by
  by_cases hta : target = a
  · subst target
    rw [ha]
    exact insertMiniCouple_left_pairs Q a b m hab
  by_cases htb : target = b
  · subst target
    rw [hb]
    exact insertMiniCouple_right_pairs Q a b m hab
  cases Q with
  | triv =>
    simp only [coupleNodes,Finset.mem_insert,Finset.mem_singleton] at ht
    exact ht.elim (fun h => (hta h).elim) (fun h => (htb h).elim)
  | type1 c r g d =>
    simp only [coupleNodes,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with ((h | hr) | hg) | hd
    · exact h.elim (fun h => (hta h).elim) (fun h => (htb h).elim)
    · have hs := red_frame_signs σ c a b ha hb
      have ih := insertMiniCouple_pairs r σ _ _ target m (redFrame_incomp c hab) hs.1 hs.2 hr
      rw [insertMiniCouple_type1_red c r g d a b target m hab hta htb hr]
      exact type1_red_constructor_perm c r _ g d a b target m _ hab hr ih
    · have hs := green_frame_signs σ a b ha hb
      have ih := insertMiniCouple_pairs g σ _ _ target m (greenFrame_incomp hab) hs.1 hs.2 hg
      rw [insertMiniCouple_type1_green c r g d a b target m hab hta htb hg]
      exact type1_green_constructor_perm c r g _ d a b target m _ hab hg ih
    · have hs := blue_frame_signs σ c a b ha hb
      have ih := insertMiniCouple_pairs d σ _ _ target m (blueFrame_incomp c hab) hs.1 hs.2 hd
      rw [insertMiniCouple_type1_blue c r g d a b target m hab hta htb hd]
      exact type1_blue_constructor_perm c r g d _ a b target m _ hab hd ih
  | type2 p n q =>
    simp only [coupleNodes,Finset.mem_union] at ht
    rcases ht with (hp | hn) | hq
    · have ih := insertMiniChain_pairs p σ 1 a target m ha hp
      rw [insertMiniCouple_type2_positive p n q a b target m hab hta htb hp]
      exact type2_positive_constructor_perm p _ n q a b target m _ hab hp ih.2 ih.1
    · have ih := insertMiniChain_pairs n σ (-1) b target m hb hn
      rw [insertMiniCouple_type2_negative p n q a b target m hab hta htb hn]
      exact type2_negative_constructor_perm p n _ q a b target m _ hab hn ih.2 ih.1
    · have hs := terminalFrame_signs σ p n a b ha hb
      have ih := insertMiniCouple_pairs q σ _ _ target m (terminalFrame_incomp p n a b hab) hs.1 hs.2 hq
      rw [insertMiniCouple_type2_terminal p n q a b target m hab hta htb hq]
      exact type2_terminal_constructor_perm p n q _ a b target m _ hab hq ih
termination_by structural Q

/-- At every chain node, both the pair list and the terminal hole match source B. -/
theorem insertMiniChain_pairs (X : RegChain) (σ : Fin w → ℤˣ) (ζ : ℤˣ)
    (a target : Fin w × Path) (m : MiniTreeCode) (ha : nodeSign σ a = ζ)
    (ht : target ∈ chainNodes X ζ a) :
    (((insertMiniChain X ζ a target m).pairsAt ζ a).Perm
      ((X.pairsAt ζ a).map (fun x =>
        (WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone x.1,WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone x.2)) ++
        (miniChain m).pairsAt (nodeSign σ target) target)) ∧
      addrExt a (insertMiniChain X ζ a target m).lonePath =
        WaveTurbulence.Reg.Skeleton.relocate target m.c m.lone (addrExt a X.lonePath) := by
  cases X with
  | nil => simp [chainNodes] at ht
  | pair k r g i s =>
    by_cases hta : target = a
    · subst target
      rw [ha]
      exact ⟨insertMiniChain_root_pairs k m r g i s ζ a,
        insertMiniChain_root_lonePath k m r g i s ζ a⟩
    by_cases htb : target = secondRoot a k i
    · subst target
      rw [nodeSign_secondRoot,ha]
      exact ⟨insertMiniChain_lower_pairs k m r g i s ζ a,
        insertMiniChain_lower_lonePath k m r g i s ζ a⟩
    simp only [chainNodes,sideNodes_eq_frame,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with (((h | hr) | hg) | hi) | hs
    · exact h.elim (fun h => (hta h).elim) (fun h => (htb h).elim)
    · have hsgn := chainRedFrame_signs σ k i ζ a ha
      have ih := insertMiniCouple_pairs r σ _ _ target m (chainRedFrame_incomp k i ζ a) hsgn.1 hsgn.2 hr
      rw [insertMiniChain_red k r g i s ζ a target m hta htb hr]
      refine ⟨chain_red_constructor_perm k r _ g i s ζ a target m _ hr ih,?_⟩
      exact (chain_side_hole_fixed k i s a target m _ _ (miniTree_slots_separate k).1
        (miniTree_slots_separate k).2.2.2.1 (orientedFrame_node_below r _ _ _ target hr)).symm
    · have hsgn := chainGreenFrame_signs σ k i ζ a ha
      have ih := insertMiniCouple_pairs g σ _ _ target m (chainGreenFrame_incomp k i ζ a) hsgn.1 hsgn.2 hg
      rw [insertMiniChain_green k r g i s ζ a target m hta htb hg]
      refine ⟨chain_green_constructor_perm k r g _ i s ζ a target m _ hg ih,?_⟩
      exact (chain_side_hole_fixed k i s a target m _ _ (miniTree_slots_separate k).2.1
        (miniTree_slots_separate k).2.2.2.2.1 (orientedFrame_node_below g _ _ _ target hg)).symm
    · have hsgn : nodeSign σ (addrExt a [k.c]) = slotSign ζ k.c := by rw [nodeSign_step,ha]
      have ih := insertMiniChain_pairs i σ (slotSign ζ k.c) (addrExt a [k.c]) target m hsgn hi
      rw [insertMiniChain_inner k r g i s ζ a target m hta htb hi]
      exact ⟨chain_inner_constructor_perm k r g i _ s ζ a target m _ hi ih.2 ih.1,
        inner_chain_hole_transport k r g i _ s ζ a target m hi ih.2⟩
    · have hsgn : nodeSign σ (backRoot a k i k.lone) = slotSign (slotSign ζ k.c) k.lone := by
        rw [backRoot_eq,nodeSign_step,nodeSign_secondRoot,ha]
      have ih := insertMiniChain_pairs s σ _ (backRoot a k i k.lone) target m hsgn hs
      rw [insertMiniChain_rest k r g i s ζ a target m hta htb hs]
      exact ⟨chain_rest_constructor_perm k r g i s _ ζ a target m _ hs ih.1,
        rest_chain_hole_transport k r g i s _ a _ ih.2⟩
termination_by structural X
end

end WaveTurbulence.Reg.Skeleton.BContext
