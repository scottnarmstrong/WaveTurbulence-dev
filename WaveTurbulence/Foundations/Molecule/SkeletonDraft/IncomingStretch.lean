/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.IncomingTransport
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.StretchChild

/-! # Incoming slot identity for prefix-relocated nodes away from the upper boundary -/

public section
namespace WaveTurbulence.Reg.Skeleton.LabelledGarden

theorem incoming_eq_of_stretch_embedding {w : ℕ} {B : Type*} (S G : LabelledGarden w B)
    (a : Address w) (p : TTree.Path) (f : GBranch S.garden.tree → GBranch G.garden.tree)
    (hf : ∀ b, (f b).1 = stretch a p b.1) (hl : ∀ b, G.label (f b) = S.label b)
    (x : GNode S.garden.tree) (y : GNode G.garden.tree)
    (hxy : y.1 = stretch a p x.1) (hx : x.1 ≠ a) : S.incoming x = G.incoming y := by
  obtain ⟨z,hz⟩ := (nodeSlotEquiv S.garden.tree).symm.surjective x
  change slotToNode S.garden.tree z = x at hz
  subst x
  cases z with
  | inl j =>
    change (GNode.root S.garden.tree j).1 ≠ a at hx
    have hn : ¬ Below a (j,[]) := by
      intro he
      have ha : a.2 = [] := List.prefix_nil.mp he.2
      exact hx (Prod.ext he.1 ha.symm)
    change y.1 = stretch a p (j,[]) at hxy
    rw [stretch_outside a p _ hn] at hxy
    have hy : y = GNode.root G.garden.tree j := Subtype.ext hxy
    rw [hy]
    exact (S.incoming_root j).trans (G.incoming_root j).symm
  | inr z =>
    obtain ⟨b,i⟩ := z
    change (b.child i).1 ≠ a at hx
    change y.1 = stretch a p (addrExt b.1 [i]) at hxy
    have hy : y = (f b).child i := by
      apply Subtype.ext
      change y.1 = addrExt (f b).1 [i]
      rw [hf b,hxy,stretch_child a b.1 p i hx]
    change S.incoming (b.child i) = _
    rw [hy,S.incoming_child,G.incoming_child,hl b]

end WaveTurbulence.Reg.Skeleton.LabelledGarden
