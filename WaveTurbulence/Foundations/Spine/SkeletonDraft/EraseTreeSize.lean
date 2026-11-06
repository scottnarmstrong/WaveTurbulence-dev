/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionTreeUpdate
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionDataCount

/-! # Exact decrease of total replacement order when a tree slot is erased -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem ReconstructionData.eraseTree_size {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (b : GBranch S.tree) :
    (D.eraseTree b).size + (D.tree b).size = D.size := by
  classical
  let E := D.eraseTree b
  have hD := Finset.sum_erase_add (s := Finset.univ) (fun c : GBranch S.tree => (D.tree c).size)
    (Finset.mem_univ b)
  have hE := Finset.sum_erase_add (s := Finset.univ) (fun c : GBranch S.tree => (E.tree c).size)
    (Finset.mem_univ b)
  have hb : (E.tree b).size = 0 := by rw [D.eraseTree_at]; rfl
  have heq : (∑ c ∈ Finset.univ.erase b, (E.tree c).size) =
      ∑ c ∈ Finset.univ.erase b, (D.tree c).size := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [D.eraseTree_other b c (Finset.ne_of_mem_erase hc)]
  change (∑ c, (E.tree c).size) + (∑ p, (D.couple p).size) + (D.tree b).size =
    (∑ c, (D.tree c).size) + ∑ p, (D.couple p).size
  omega

end WaveTurbulence.Reg.Skeleton
