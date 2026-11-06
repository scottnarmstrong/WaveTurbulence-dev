/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.ChainDecorationBlocks
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Raw

/-! # Exact decoration lookup at a canonical finite frame slot -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

noncomputable def decorationAt {w : ℕ} (L : List (Decoration w)) (p : Pair w)
    (hp : p ∈ L.map Prod.fst) : Decoration w :=
  Classical.choose (List.mem_map.mp hp)

theorem decorationAt_mem {w : ℕ} (L : List (Decoration w)) (p : Pair w) (hp : p ∈ L.map Prod.fst) :
    decorationAt L p hp ∈ L := (Classical.choose_spec (List.mem_map.mp hp)).1

theorem decorationAt_frame {w : ℕ} (L : List (Decoration w)) (p : Pair w) (hp : p ∈ L.map Prod.fst) :
    (decorationAt L p hp).1 = p := (Classical.choose_spec (List.mem_map.mp hp)).2

theorem decorationAt_eq {w : ℕ} (L : List (Decoration w)) (hL : (L.map Prod.fst).Nodup)
    (p : Pair w) (hp : p ∈ L.map Prod.fst) (e : Decoration w) (he : e ∈ L) (hf : e.1 = p) :
    decorationAt L p hp = e := by
  exact List.inj_on_of_nodup_map hL (decorationAt_mem L p hp) he
    ((decorationAt_frame L p hp).trans hf.symm)

end WaveTurbulence.Reg.Skeleton
