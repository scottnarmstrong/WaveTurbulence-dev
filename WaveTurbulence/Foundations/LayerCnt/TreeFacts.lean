/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.GardenParents
import Mathlib.Tactic

/-! # Elementary tree facts for the exit argument (TARGET layervine, L1531)

Descendants and parents of branching nodes and leaves.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

theorem branch_ne_leaf {G : Garden w} (b : GBranch G.tree) (ℓ : GLeaf G.tree) : b.1 ≠ ℓ.1 := by
  intro h
  have hj : b.1.1 = ℓ.1.1 := congrArg Prod.fst h
  have hp : b.1.2 = ℓ.1.2 := congrArg Prod.snd h
  have h1 := b.2
  have h2 := ℓ.2
  rw [hj, hp] at h1
  exact TTree.not_mem_branching_of_mem_leaves _ h2 h1

theorem parent_isDesc {G : Garden w} (x : GNode G.tree) (hx : x.1.2 ≠ []) :
    (GNode.parent x hx).toNode.IsDesc x := by
  refine ⟨rfl, ?_⟩
  show x.1.2.dropLast <+: x.1.2
  exact List.dropLast_prefix _

theorem isDesc_parent_of_ne {G : Garden w} {a x : GNode G.tree} (hx : x.1.2 ≠ []) (hax : a.IsDesc x)
    (hne : a.1.2 ≠ x.1.2) : a.IsDesc (GNode.parent x hx).toNode := by
  obtain ⟨hj, q, hq⟩ : a.1.1 = x.1.1 ∧ ∃ q, a.1.2 ++ q = x.1.2 := hax
  have hq0 : q ≠ [] := by
    rintro rfl
    exact hne (by simpa using hq)
  refine ⟨hj, q.dropLast, ?_⟩
  show a.1.2 ++ q.dropLast = x.1.2.dropLast
  rw [← hq, List.dropLast_append_of_ne_nil hq0]

theorem branch_isDesc_leaf_iff {G : Garden w} (b : GBranch G.tree) (ℓ : GLeaf G.tree) (h : ℓ.1.2 ≠ []) :
    b.toNode.IsDesc ℓ.toNode ↔ b.toNode.IsDesc (GNode.parent ℓ.toNode h).toNode := by
  constructor
  · intro hb
    exact isDesc_parent_of_ne h hb (fun he => branch_ne_leaf b ℓ (Prod.ext (by
      have := hb.1; exact this) he))
  · intro hb
    exact hb.trans (parent_isDesc ℓ.toNode h)

end WaveTurbulence.LayerCnt
