/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.RawChainIdentity

/-! # Exact endpoint transport through outer, inner and remaining bare chain insertions -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem stretch_outer_inner_rest {w : ℕ} (a z : Address w) (c l : Fin 3) (p q : Path) :
    stretch (addrExt a ([c] ++ p ++ [l])) q
      (stretch (addrExt a [c]) p (stretch a [c,l] z)) =
        stretch a ([c] ++ p ++ [l] ++ q) z := by
  by_cases hz : Below a z
  · obtain ⟨r,rfl⟩ := below_exists_frame a z hz
    rw [stretch_frame]
    have h1 : addrExt a ([c,l] ++ r) = addrExt (addrExt a [c]) ([l] ++ r) := by
      rw [addrExt_append]
      rfl
    rw [h1,stretch_frame]
    have h2 : addrExt (addrExt a [c]) (p ++ ([l] ++ r)) =
        addrExt (addrExt a ([c] ++ p ++ [l])) r := by
      simp only [addrExt,List.append_assoc]
    rw [h2,stretch_frame,stretch_frame]
    simp only [addrExt,List.append_assoc]
  · have h1 : ¬ Below (addrExt a [c]) z := fun h => hz (below_trans (below_extend _ _) h)
    have h2 : ¬ Below (addrExt a ([c] ++ p ++ [l])) z := fun h => hz (below_trans (below_extend _ _) h)
    rw [stretch_outside a _ z hz,stretch_outside _ _ z h1,stretch_outside _ _ z h2,
      stretch_outside a _ z hz]

end WaveTurbulence.Reg.Skeleton
