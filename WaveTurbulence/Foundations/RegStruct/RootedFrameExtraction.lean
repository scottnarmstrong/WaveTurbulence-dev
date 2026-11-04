/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainSubtreeFrames

/-! # Sign-oriented extraction frames inside actual rooted subtrees -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Subtree extraction at a global extension composes with actual extraction at its root. -/
theorem subtree_addrExt {w : ℕ} (tree : Fin w → TTree) (a : Fin w × Path) (u : TTree)
    (hu : Comb.subtree (tree a.1) a.2 = some u) (p : Path) :
    Comb.subtree (tree (addrExt a p).1) (addrExt a p).2 = Comb.subtree u p := by
  change Comb.subtree (tree a.1) (a.2 ++ p) = _
  rw [Comb.subtree_append,hu]
  rfl

/-- Physical side-root extractions become positive/negative extractions after orientation. -/
theorem orientedFrame_extraction {w : ℕ} (F : (Fin w × Path) → Option TTree)
    (C : RegCpl) (ε : ℤˣ) (front back : Fin w × Path)
    (hf : F front = some (treeOfSign C.trees ε))
    (hb : F back = some (treeOfSign C.trees (-ε))) :
    F (orientedFrame ε front back).1 = some C.trees.1 ∧
      F (orientedFrame ε front back).2 = some C.trees.2 := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · constructor
    · simpa [orientedFrame,treeOfSign] using hf
    · simpa [orientedFrame,treeOfSign] using hb
  · constructor
    · simpa [orientedFrame,treeOfSign] using hb
    · simpa [orientedFrame,treeOfSign] using hf

/-- Actual extraction of both red side trees through an arbitrary enclosing root. -/
theorem chain_red_frame_extraction {w : ℕ} (tree : Fin w → TTree) (a : Fin w × Path)
    (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h)) :
    Comb.subtree (tree (chainRedFrame k i ζ a).1.1) (chainRedFrame k i ζ a).1.2 = some r.trees.1 ∧
      Comb.subtree (tree (chainRedFrame k i ζ a).2.1) (chainRedFrame k i ζ a).2.2 = some r.trees.2 := by
  apply orientedFrame_extraction (fun z => Comb.subtree (tree z.1) z.2) r (slotSign ζ k.red.1)
  · rw [subtree_addrExt tree a _ ha]
    exact chain_red_front_subtree k r g i s ζ h
  · rw [subtree_addrExt tree a _ ha]
    exact chain_red_back_subtree k r g i s ζ h

/-- Actual extraction of both green side trees through an arbitrary enclosing root. -/
theorem chain_green_frame_extraction {w : ℕ} (tree : Fin w → TTree) (a : Fin w × Path)
    (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (ζ : ℤˣ) (h : TTree)
    (ha : Comb.subtree (tree a.1) a.2 = some ((RegChain.pair k r g i s).plug ζ h)) :
    Comb.subtree (tree (chainGreenFrame k i ζ a).1.1) (chainGreenFrame k i ζ a).1.2 = some g.trees.1 ∧
      Comb.subtree (tree (chainGreenFrame k i ζ a).2.1) (chainGreenFrame k i ζ a).2.2 = some g.trees.2 := by
  apply orientedFrame_extraction (fun z => Comb.subtree (tree z.1) z.2) g (slotSign ζ k.green.1)
  · rw [subtree_addrExt tree a _ ha]
    exact chain_green_front_subtree k r g i s ζ h
  · rw [subtree_addrExt tree a _ ha]
    exact chain_green_back_subtree k r g i s ζ h

end WaveTurbulence.Reg
