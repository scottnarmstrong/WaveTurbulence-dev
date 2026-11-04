/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeRootClocks

/-! # The source lone parent is exactly the final selected branching clock -/

public section
noncomputable section
namespace WaveTurbulence.IncohInst
open Incoh Links

@[expose] def TreeClockSelection.parentBranch {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) : GBranch G.tree :=
  treeLinkEquiv hX (C.selection.coordinates.rootVertex (Fin.last (C.m + 1)))

/-- The marked source lone leaf is exactly the code's lone path. -/
theorem tree_lone_path {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G)
    (ℓ : GLeaf G.tree) (hl : G.IsLone ℓ) : ℓ.val.2 = X.lonePath := by
  by_contra hn
  have hm := hX.2.1 ℓ
  rw [ite_eq_right hn] at hm
  have hh : G.mark ℓ = some MarkTag.lower := hl
  rw [hm] at hh
  contradiction

/-- The original source lone-parent predicate has exactly one branching clock. -/
theorem TreeClockSelection.isLoneParent_iff {G : Garden 1} {X : RegChain}
    {hX : X.DecodesTree G} (C : TreeClockSelection hX) (b : GBranch G.tree) :
    G.IsLoneParent b ↔ b = C.parentBranch := by
  constructor
  · rintro ⟨ℓ, hl, _, j, hj⟩
    have hp := tree_lone_path hX ℓ hl
    obtain ⟨i, hi⟩ := C.last_parent
    have hh : b.val.2 ++ [j] = C.parentBranch.val.2 ++ [i] :=
      hj.symm.trans (hp.trans (congrArg Prod.snd hi))
    apply Subtype.ext
    exact Prod.ext (Subsingleton.elim _ _) (List.append_inj' hh rfl).1
  · rintro rfl
    refine ⟨loneLeaf hX, ?_, ?_⟩
    · change G.mark (loneLeaf hX) = some MarkTag.lower
      rw [hX.2.1]
      simp only [loneLeaf, ite_true]
    · obtain ⟨i, hi⟩ := C.last_parent
      exact ⟨Subsingleton.elim _ _, i, congrArg Prod.snd hi⟩

end WaveTurbulence.IncohInst
