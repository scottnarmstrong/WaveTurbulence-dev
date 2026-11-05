/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionCoupleUpdate

/-! # Exact replacement order removed by erasing a couple slot -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseCouple_size {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (p : SourcePair S) :
    (D.eraseCouple p).size + (D.couple p).size = D.size := by
  classical
  let E := D.eraseCouple p
  have hD := Finset.sum_erase_add (s := Finset.univ) (fun q : SourcePair S => (D.couple q).size)
    (Finset.mem_univ p)
  have hE := Finset.sum_erase_add (s := Finset.univ) (fun q : SourcePair S => (E.couple q).size)
    (Finset.mem_univ p)
  have hp : (E.couple p).size = 0 := by rw [D.eraseCouple_at]; rfl
  have heq : (∑ q ∈ Finset.univ.erase p, (E.couple q).size) =
      ∑ q ∈ Finset.univ.erase p, (D.couple q).size := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [D.eraseCouple_other p q (Finset.ne_of_mem_erase hq)]
  change (∑ b, (D.tree b).size) + (∑ q, (E.couple q).size) + (D.couple p).size =
    (∑ b, (D.tree b).size) + ∑ q, (D.couple q).size
  omega

end WaveTurbulence.Reg.Skeleton
