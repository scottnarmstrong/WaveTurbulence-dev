/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.IncomingStretch

/-! # The upper boundary retains its original incoming slot during prefix collapse -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem incoming_stretch_boundary {w : ℕ} {B : Type*} (S G : LabelledGarden w B)
    (a : GNode G.garden.tree) (p : TTree.Path)
    (f : GBranch S.garden.tree → GBranch G.garden.tree)
    (hf : ∀ b, (f b).1 = stretch a.1 p b.1) (hl : ∀ b, G.label (f b) = S.label b)
    (x : GNode S.garden.tree) (hx : x.1 = a.1) : S.incoming x = G.incoming a := by
  obtain ⟨z,hz⟩ := (nodeSlotEquiv S.garden.tree).symm.surjective x
  change slotToNode S.garden.tree z = x at hz
  subst x
  cases z with
  | inl j =>
    have ha : a = GNode.root G.garden.tree j := Subtype.ext hx.symm
    rw [ha]
    exact (S.incoming_root j).trans (G.incoming_root j).symm
  | inr z =>
    obtain ⟨b,i⟩ := z
    change (b.child i).1 = a.1 at hx
    have hn : ¬ Below a.1 b.1 := by
      intro he
      have hh := he.2.length_le
      have hh' := congrArg (fun z : Address w => z.2.length) hx
      change (b.1.2 ++ [i]).length = a.1.2.length at hh'
      simp only [List.length_append,List.length_singleton] at hh'
      omega
    have hb : (f b).1 = b.1 := (hf b).trans (stretch_outside a.1 p b.1 hn)
    have ha : a = (f b).child i := by
      apply Subtype.ext
      change a.1 = addrExt (f b).1 [i]
      rw [hb,← hx]
      rfl
    change S.incoming (b.child i) = _
    rw [ha,S.incoming_child,G.incoming_child,hl b]

end WaveTurbulence.Reg.Skeleton.LabelledGarden
