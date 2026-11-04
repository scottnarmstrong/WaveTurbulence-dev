/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.FrameStability

/-! # Oriented side-couple frames of a chain pair -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Order two roots so that the first one has positive sign. -/
def orientedFrame {w : ℕ} (ε : ℤˣ) (front back : Fin w × Path) :=
  if ε = 1 then (front,back) else (back,front)

abbrev chainRedFrame {w : ℕ} (k : MiniTreeCode) (i : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :=
  orientedFrame (slotSign ζ k.red.1) (addrExt a [k.red.1]) (backRoot a k i k.red.2)

abbrev chainGreenFrame {w : ℕ} (k : MiniTreeCode) (i : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :=
  orientedFrame (slotSign ζ k.green.1) (addrExt a [k.green.1]) (backRoot a k i k.green.2)

/-- Orientation does not change the underlying incomparable pair of roots. -/
theorem orientedFrame_incomp {w : ℕ} (ε : ℤˣ) (front back : Fin w × Path)
    (h : IncompAddr front back) :
    IncompAddr (orientedFrame ε front back).1 (orientedFrame ε front back).2 := by
  by_cases he : ε = 1
  · simpa only [orientedFrame,he,ite_true] using h
  · simpa only [orientedFrame,he,ite_false] using h.symm

/-- The sign-oriented frame really has signs positive and negative. -/
theorem orientedFrame_signs (σ : Fin 2 → ℤˣ) (ε : ℤˣ) (front back : Fin 2 × Path)
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

/-- Swapping either frame preserves separation from another complete frame. -/
theorem FramesApart.orient {w : ℕ} {F G : (Fin w × Path) × (Fin w × Path)}
    (h : FramesApart F G) (ε η : ℤˣ) :
    FramesApart (orientedFrame ε F.1 F.2) (orientedFrame η G.1 G.2) := by
  by_cases he : ε = 1 <;> by_cases hh : η = 1 <;>
    simp only [orientedFrame,he,hh,ite_true,ite_false]
  · exact h
  · exact ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩
  · exact ⟨h.2.2.1,h.2.2.2,h.1,h.2.1⟩
  · exact ⟨h.2.2.2,h.2.2.1,h.2.1,h.1⟩

/-- Side-pair blocks use exactly the sign-oriented root frame. -/
theorem sidePairs_eq_frame {w : ℕ} (Q : RegCpl) (ε : ℤˣ) (front back : Fin w × Path) :
    sidePairs Q ε front back = Q.pairsAt (orientedFrame ε front back).1 (orientedFrame ε front back).2 := by
  by_cases he : ε = 1 <;> simp only [sidePairs,orientedFrame,he,ite_true,ite_false]

/-- The conditional side insertion is the same operation at the oriented frame. -/
theorem insertMiniCouple_orientedFrame {w : ℕ} (Q : RegCpl) (ε : ℤˣ)
    (front back target : Fin w × Path) (m : MiniTreeCode) :
    (if ε = 1 then insertMiniCouple Q front back target m else insertMiniCouple Q back front target m) =
      insertMiniCouple Q (orientedFrame ε front back).1 (orientedFrame ε front back).2 target m := by
  by_cases he : ε = 1 <;> simp only [orientedFrame,he,ite_true,ite_false]

/-- The conditional side node set is exactly the node set in its oriented frame. -/
theorem sideNodes_eq_frame {w : ℕ} (Q : RegCpl) (ε : ℤˣ) (front back : Fin w × Path) :
    (if ε = 1 then coupleNodes Q front back else coupleNodes Q back front) =
      coupleNodes Q (orientedFrame ε front back).1 (orientedFrame ε front back).2 := by
  by_cases he : ε = 1 <;> simp only [orientedFrame,he,ite_true,ite_false]

/-- Every side node lies below one of the two physical roots, independent of orientation. -/
theorem orientedFrame_node_below {w : ℕ} (Q : RegCpl) (ε : ℤˣ)
    (front back target : Fin w × Path)
    (ht : target ∈ coupleNodes Q (orientedFrame ε front back).1 (orientedFrame ε front back).2) :
    Below front target ∨ Below back target := by
  by_cases he : ε = 1
  · simp only [orientedFrame,he,ite_true] at ht
    exact coupleNodes_below Q _ _ _ ht
  · simp only [orientedFrame,he,ite_false] at ht
    exact (coupleNodes_below Q _ _ _ ht).symm

/-- The red frame is a genuine two-root frame. -/
theorem chainRedFrame_incomp {w : ℕ} (k : MiniTreeCode) (i : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    IncompAddr (chainRedFrame k i ζ a).1 (chainRedFrame k i ζ a).2 := by
  apply orientedFrame_incomp
  exact incomp_distinct_children a k.red.1 k.c [] (i.lonePath ++ [k.red.2]) (miniTree_slots_separate k).1

/-- The green frame is a genuine two-root frame. -/
theorem chainGreenFrame_incomp {w : ℕ} (k : MiniTreeCode) (i : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    IncompAddr (chainGreenFrame k i ζ a).1 (chainGreenFrame k i ζ a).2 := by
  apply orientedFrame_incomp
  exact incomp_distinct_children a k.green.1 k.c [] (i.lonePath ++ [k.green.2]) (miniTree_slots_separate k).2.1

/-- Red and green side-couple frames are disjoint, including all their descendants. -/
theorem chain_red_green_apart {w : ℕ} (k : MiniTreeCode) (i : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    FramesApart (chainRedFrame k i ζ a) (chainGreenFrame k i ζ a) := by
  apply FramesApart.orient (F := (addrExt a [k.red.1],backRoot a k i k.red.2))
    (G := (addrExt a [k.green.1],backRoot a k i k.green.2))
  refine ⟨incomp_distinct_children a _ _ [] [] (miniTree_slots_separate k).2.2.1,
    incomp_distinct_children a _ _ [] _ (miniTree_slots_separate k).1,
    incomp_distinct_children a _ _ _ [] (miniTree_slots_separate k).2.1.symm,?_⟩
  rw [backRoot_eq,backRoot_eq]
  exact incomp_distinct_children (secondRoot a k i) _ _ [] [] (miniTree_slots_separate k).2.2.2.2.2

/-- The sign data required to recurse into the red side couple. -/
theorem chainRedFrame_signs (σ : Fin 2 → ℤˣ) (k : MiniTreeCode) (i : RegChain) (ζ : ℤˣ)
    (a : Fin 2 × Path) (ha : nodeSign σ a = ζ) :
    nodeSign σ (chainRedFrame k i ζ a).1 = 1 ∧ nodeSign σ (chainRedFrame k i ζ a).2 = -1 := by
  apply orientedFrame_signs
  · rw [nodeSign_step,ha]
  · rw [nodeSign_chain_child,ha,slotSign_red]

/-- The sign data required to recurse into the green side couple. -/
theorem chainGreenFrame_signs (σ : Fin 2 → ℤˣ) (k : MiniTreeCode) (i : RegChain) (ζ : ℤˣ)
    (a : Fin 2 × Path) (ha : nodeSign σ a = ζ) :
    nodeSign σ (chainGreenFrame k i ζ a).1 = 1 ∧ nodeSign σ (chainGreenFrame k i ζ a).2 = -1 := by
  apply orientedFrame_signs
  · rw [nodeSign_step,ha]
  · rw [nodeSign_chain_child,ha,slotSign_green]

end WaveTurbulence.Reg
