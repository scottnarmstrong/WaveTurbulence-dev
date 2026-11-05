/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.EraseTreeUpperPosition
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.StretchDescendantExtension
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionMonotone

/-! # Exact descendant attachment transport when one tree context is erased -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem ReconstructionData.eraseTree_position_descendant {w : ℕ} {S : Garden w}
    (D : ReconstructionData S) (b : GBranch S.tree) (a : GNode S.tree)
    (hab : Below b.1 a.1) (hne : a ≠ b.toNode) :
    inflatedPosition S D.tree a =
      stretch (inflatedPosition S (D.eraseTree b).tree b.toNode) (D.tree b).lonePath
        (inflatedPosition S (D.eraseTree b).tree a) := by
  let E := D.eraseTree b
  let A := inflatedPosition S E.tree b.toNode
  have hp : a.1.2 ≠ [] := by
    intro he
    have hb : b.1.2 = [] := List.prefix_nil.mp (he ▸ hab.2)
    exact hne (Subtype.ext (Prod.ext hab.1 (he.trans hb.symm)))
  let c := a.parent hp
  let i := a.1.2.getLast hp
  have hchild : c.child i = a := child_parent a hp
  have hv : addrExt c.1 [i] = a.1 := congrArg (fun z : GNode S.tree => z.1) hchild
  have hac : Below b.1 c.1 := (below_child_iff b.1 c.1 i (fun he =>
    hne (Subtype.ext (hv.symm.trans he)))).mp (hv.symm ▸ hab)
  have hd : inflatedPosition S D.tree a =
      addrExt (inflatedPosition S D.tree c.toNode) ((D.tree c).lonePath ++ [i]) :=
    (congrArg (inflatedPosition S D.tree) hchild.symm).trans (inflatedPosition_child S D.tree c i)
  have he : inflatedPosition S E.tree a =
      addrExt (inflatedPosition S E.tree c.toNode) ((E.tree c).lonePath ++ [i]) :=
    (congrArg (inflatedPosition S E.tree) hchild.symm).trans (inflatedPosition_child S E.tree c i)
  by_cases hcb : c = b
  · have hd' : inflatedPosition S D.tree a = addrExt (inflatedPosition S D.tree b.toNode)
        ((D.tree b).lonePath ++ [i]) := hd.trans (congrArg
          (fun c : GBranch S.tree => addrExt (inflatedPosition S D.tree c.toNode) ((D.tree c).lonePath ++ [i])) hcb)
    have he' : inflatedPosition S E.tree a = addrExt (inflatedPosition S E.tree b.toNode)
        ((E.tree b).lonePath ++ [i]) := he.trans (congrArg
          (fun c : GBranch S.tree => addrExt (inflatedPosition S E.tree c.toNode) ((E.tree c).lonePath ++ [i])) hcb)
    have hbase : inflatedPosition S D.tree b.toNode = A := (D.eraseTree_position_at b).symm
    have hnil : E.tree b = .nil := D.eraseTree_at b
    calc
      _ = addrExt A ((D.tree b).lonePath ++ [i]) := hd'.trans (congrArg (fun z => addrExt z ((D.tree b).lonePath ++ [i])) hbase)
      _ = stretch A (D.tree b).lonePath (addrExt A [i]) := (stretch_frame A _ [i]).symm
      _ = _ := congrArg (stretch A (D.tree b).lonePath) (by
        have hh := he'
        rw [hnil] at hh
        exact hh.symm)
  · have hcn : c.toNode ≠ b.toNode := fun h => hcb (Subtype.ext (congrArg (fun z : GNode S.tree => z.1) h))
    have ih := D.eraseTree_position_descendant b c.toNode hac hcn
    have hcode : D.tree c = E.tree c := (D.eraseTree_other b c hcb).symm
    have hbelow : Below A (inflatedPosition S E.tree c.toNode) := inflatedPosition_below S E.tree b.toNode c.toNode hac
    exact hd.trans ((congrArg₂ addrExt ih (congrArg (fun X : RegChain => X.lonePath ++ [i]) hcode)).trans
      ((stretch_addrExt_of_below A (inflatedPosition S E.tree c.toNode) (D.tree b).lonePath
        ((E.tree c).lonePath ++ [i]) hbelow).symm.trans
        (congrArg (stretch A (D.tree b).lonePath) he.symm)))
termination_by a.1.2.length
decreasing_by
  change a.1.2.dropLast.length < a.1.2.length
  rw [List.length_dropLast]
  have hn : a.1.2.length ≠ 0 := fun he => hp (List.length_eq_zero_iff.mp he)
  omega

end WaveTurbulence.Reg.Skeleton
