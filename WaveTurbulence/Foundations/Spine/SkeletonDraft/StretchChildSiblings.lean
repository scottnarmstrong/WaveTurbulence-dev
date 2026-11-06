/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ChainSpineStretch
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.MiniLeafRegion

/-! # Prefix insertion in one child leaves every sibling attachment fixed -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem stretch_child_sibling {w : ℕ} (a : Address w) (c i : Fin 3) (p : Path) (hi : i ≠ c) :
    stretch (addrExt a [c]) p (addrExt a [i]) = addrExt a [i] := by
  apply stretch_outside
  intro h
  have hp := (below_frames_iff a [c] [i]).mp h
  have he := hp.eq_of_length (by simp)
  exact hi (List.singleton_inj.mp he).symm

theorem stretch_child_descendant {w : ℕ} (a : Address w) (c i : Fin 3) (p : Path) :
    stretch (addrExt a [c]) p (addrExt a [c,i]) = addrExt a ([c] ++ p ++ [i]) := by
  have he : addrExt a [c,i] = addrExt (addrExt a [c]) [i] := by
    rw [addrExt_append]
    rfl
  rw [he,stretch_frame]
  simp only [addrExt,List.append_assoc]

end WaveTurbulence.Reg.Skeleton
