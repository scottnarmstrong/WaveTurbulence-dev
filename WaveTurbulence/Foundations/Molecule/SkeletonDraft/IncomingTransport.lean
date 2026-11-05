/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.IncomingPorts

/-! # Incoming slots under an actual address-preserving branch embedding -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

/-- If actual surviving branch addresses and labels agree, every surviving incoming node slot agrees. -/
theorem incoming_eq_of_branch_embedding {w : ℕ} {B : Type*} (S G : LabelledGarden w B)
    (f : GBranch S.garden.tree → GBranch G.garden.tree)
    (hf : ∀ b, (f b).1 = b.1) (hl : ∀ b, G.label (f b) = S.label b)
    (x : GNode S.garden.tree) (y : GNode G.garden.tree) (hxy : x.1 = y.1) :
    S.incoming x = G.incoming y := by
  obtain ⟨z,hz⟩ := (nodeSlotEquiv S.garden.tree).symm.surjective x
  change slotToNode S.garden.tree z = x at hz
  subst x
  cases z with
  | inl j =>
    change (GNode.root S.garden.tree j).1 = y.1 at hxy
    have hy : y = GNode.root G.garden.tree j := Subtype.ext hxy.symm
    rw [hy]
    exact (S.incoming_root j).trans (G.incoming_root j).symm
  | inr z =>
    obtain ⟨b,i⟩ := z
    change (b.child i).1 = y.1 at hxy
    have hy : y = (f b).child i := by
      apply Subtype.ext
      change y.1 = ((f b).1.1,(f b).1.2 ++ [i])
      rw [hf b,← hxy]
      rfl
    change S.incoming (b.child i) = _
    rw [hy,S.incoming_child,G.incoming_child,hl b]

end WaveTurbulence.Reg.Skeleton.LabelledGarden
