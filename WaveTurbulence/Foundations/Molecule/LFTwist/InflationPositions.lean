/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ReconstructionLookup

/-! # Raw inflation frames are the exact actual reconstruction addresses -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton
variable {w : ℕ} {S : Garden w}

theorem inflationFrame_singleton (X : Address w → RegChain) (a : Address w) (i : Fin 3) :
    inflationFrame X a [i] = (X a).lonePath ++ [i] := by
  simp only [inflationFrame, List.append_nil]

/-- The exact expanded address read down a literal source path. -/
@[expose] noncomputable def rawSourcePosition (D : ReconstructionData S) (a : Address w) : Address w :=
  addrExt (a.1,[]) (inflationFrame (branchLookup D) (a.1,[]) a.2)

theorem rawSourcePosition_child (D : ReconstructionData S) (b : GBranch S.tree) (i : Fin 3) :
    rawSourcePosition D (b.child i).1 =
      addrExt (rawSourcePosition D b.1) ((D.tree b).lonePath ++ [i]) := by
  have hb : addrExt (b.1.1,[]) b.1.2 = b.1 := Prod.ext rfl (List.nil_append _)
  change addrExt (b.1.1,[]) (inflationFrame (branchLookup D) (b.1.1,[]) (b.1.2 ++ [i])) =
    addrExt (addrExt (b.1.1,[]) (inflationFrame (branchLookup D) (b.1.1,[]) b.1.2))
      ((D.tree b).lonePath ++ [i])
  rw [inflationFrame_append, hb, inflationFrame_singleton, branchLookup_branch]
  exact (addrExt_append _ _ _).symm

/-- The raw down-path definition and C3's actual parent-recursive address coincide. -/
theorem inflatedPosition_eq_rawSourcePosition (D : ReconstructionData S) (a : GNode S.tree) :
    inflatedPosition S D.tree a = rawSourcePosition D a.1 := by
  rw [inflatedPosition]
  split_ifs with h
  · change a.1 = addrExt (a.1.1,[]) (inflationFrame (branchLookup D) (a.1.1,[]) a.1.2)
    rw [h]
    exact Prod.ext rfl h
  · let b := a.parent h
    let i := a.1.2.getLast h
    have hc : b.child i = a := child_parent a h
    have hh := inflatedPosition_eq_rawSourcePosition D b.toNode
    rw [hh]
    exact (rawSourcePosition_child D b i).symm.trans
      (congrArg (rawSourcePosition D) (congrArg (fun z : GNode S.tree => z.1) hc))
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  have hp : a.1.2.length ≠ 0 := fun he => h (List.length_eq_zero_iff.mp he)
  rw [List.length_dropLast]
  omega

end WaveTurbulence.LFTwist
