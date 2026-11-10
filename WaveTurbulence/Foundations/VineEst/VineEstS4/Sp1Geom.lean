/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Rg5SSum

/-! # The split geometry of a twist at a member below the split joint (V5 Step 4b, step 4, WP-D part 1)

`rigidAt_of_split`: for blocks `S` (joints `a`, `b`) and `T` (joints `b`, `c`) with `S ∩ T = {b}` and a unit twist whose atom set
`At` lies in `T` (the vine of a member BELOW the split joint), with lower joint `≠ b`, the upper block `S` is rigid
(`RigidAt P S b`): its atoms other than `b` have no child equal to the lower joint or to the partner of the retained leaf.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree

variable {w : ℕ} {G : Garden w} {S T At : Finset (GBranch G.tree)} {b c : GBranch G.tree}

theorem rigidAt_of_split (hT : G.molecule.IsBlock T b c) (hi : S ∩ T = {b})
    (hCLT : Mole.CLParentPattern G T b c) (P : CorePlacement G) (hP : IsPlacementAt G At P.lower P) (hAt : At ⊆ T)
    (hlowAt : P.lower ∈ At) (hlowb : P.lower ≠ b) : RigidAt P S b := by
  have hlowT : P.lower ∈ T := hAt hlowAt
  have hlowS : P.lower ∉ S := fun h => hlowb (Finset.mem_singleton.mp (hi ▸ Finset.mem_inter.mpr ⟨h, hlowT⟩))
  have hpar : Mole.InternalParent G T P.lower := by
    by_cases hc : P.lower = c
    · exact hc ▸ hCLT.2
    · exact Mole.block_interior_has_parent G hT hlowT hlowb hc
  have hSb : ∀ v ∈ S.erase b, v ∉ T := fun v hv hvT =>
    (Finset.mem_erase.mp hv).1 (Finset.mem_singleton.mp (hi ▸ Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hv).2, hvT⟩))
  refine ⟨hlowS, fun v hv i hc => ?_, fun v hv i hc => ?_⟩
  · obtain ⟨hn, hp⟩ := hpar
    have := parent_eq_of_child (n := P.lower.toNode) hn (p := v) (i := i) hc.symm
    exact hSb v hv (this ▸ hp)
  · have hp := hAt (placement_paired_parent_mem G P hP)
    have := parent_eq_of_child (n := (G.pair P.retained).toNode) P.paired_nonroot (p := v) (i := i) hc.symm
    exact hSb v hv (this ▸ hp)

end WaveTurbulence.VineEstS4
