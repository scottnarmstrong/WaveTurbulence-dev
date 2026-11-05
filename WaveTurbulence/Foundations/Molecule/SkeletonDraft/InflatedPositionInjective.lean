/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedPositionSeparation

/-! # Literal attachment positions embed the complete actual source node set -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem inflatedPosition_ne_of_desc {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain)
    (a b : GNode S.tree) (hab : Below a.1 b.1) (hne : a ≠ b) :
    inflatedPosition S X a ≠ inflatedPosition S X b := by
  have hb : b.1.2 ≠ [] := by
    intro hb
    have ha : a.1.2 = [] := List.prefix_nil.mp (by simpa only [hb] using hab.2)
    exact hne (Subtype.ext (Prod.ext hab.1.symm (ha.trans hb.symm)))
  let d := b.parent hb
  let i := b.1.2.getLast hb
  have hc : d.child i = b := child_parent b hb
  have hcv : addrExt d.1 [i] = b.1 := congrArg (fun z : GNode S.tree => z.1) hc
  have hn : addrExt d.1 [i] ≠ a.1 := fun hh => hne (Subtype.ext (hh.symm.trans hcv))
  have hd : Below a.1 d.1 := (below_child_iff a.1 d.1 i hn).mp (by rw [hcv]; exact hab)
  have hm := (inflatedPosition_below S X a d.toNode hd).2.length_le
  have hl := congrArg (fun z : Address w => z.2.length) (inflatedPosition_child S X d i)
  rw [hc] at hl
  change (inflatedPosition S X b).2.length =
    ((inflatedPosition S X d.toNode).2 ++ ((X d).lonePath ++ [i])).length at hl
  simp only [List.length_append,List.length_singleton] at hl
  intro he
  have he' := congrArg (fun z : Address w => z.2.length) he
  omega

/-- Every source node has a distinct literal replacement attachment address. -/
theorem inflatedPosition_injective {w : ℕ} (S : Garden w) (X : GBranch S.tree → RegChain) :
    Function.Injective (inflatedPosition S X) := by
  intro a b he
  by_contra hn
  by_cases hab : Below a.1 b.1
  · exact inflatedPosition_ne_of_desc S X a b hab hn he
  by_cases hba : Below b.1 a.1
  · exact inflatedPosition_ne_of_desc S X b a hba (Ne.symm hn) he.symm
  have hi := inflatedPosition_incomp S X a b ⟨hab,hba⟩
  apply hi.1
  rw [he]
  exact ⟨rfl,List.prefix_refl _⟩

/-- A proper descendant of a branching root lies below one of its actual ordered children. -/
theorem below_child_of_desc_ne {w : ℕ} {tree : Fin w → TTree} (a : GBranch tree) (b : GNode tree)
    (hab : Below a.1 b.1) (hne : a.toNode ≠ b) : ∃ i : Fin 3, Below (a.child i).1 b.1 := by
  obtain ⟨r,hr⟩ := hab.2
  cases r with
  | nil =>
    have hp : a.1.2 = b.1.2 := by simpa only [List.append_nil] using hr
    have he : a.toNode = b := Subtype.ext (Prod.ext hab.1.symm hp)
    exact (hne he).elim
  | cons i r =>
    refine ⟨i,hab.1,?_⟩
    change a.1.2 ++ [i] <+: b.1.2
    exact ⟨r,by simpa only [List.append_assoc,List.singleton_append] using hr⟩

end WaveTurbulence.Reg.Skeleton
