/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PrefixStretch

/-! # Arbitrary extension naturality below a prefix-insertion boundary -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem stretch_addrExt_of_below {w : ℕ} (a d : Address w) (p q : Path) (hd : Below a d) :
    stretch a p (addrExt d q) = addrExt (stretch a p d) q := by
  obtain ⟨r,rfl⟩ := below_exists_frame a d hd
  rw [addrExt_append,stretch_frame,stretch_frame,addrExt_append]
  exact congrArg (addrExt a) (List.append_assoc p r q).symm

end WaveTurbulence.Reg.Skeleton
