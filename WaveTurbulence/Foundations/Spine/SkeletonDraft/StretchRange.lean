/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.CollapseIncomingRedirect
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBCollapse

/-! # A nonempty inserted prefix never maps a surviving node to the removed upper root -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem stretch_ne_upper {w : ℕ} (a x : Address w) (p : Path) (hp : p ≠ []) :
    stretch a p x ≠ a := by
  by_cases hx : Below a x
  · obtain ⟨r,rfl⟩ := below_exists_frame a x hx
    rw [stretch_frame]
    intro he
    have hl := congrArg (fun z : Address w => z.2.length) he
    change (a.2 ++ (p ++ r)).length = a.2.length at hl
    have hp' : p.length ≠ 0 := fun he => hp (List.length_eq_zero_iff.mp he)
    simp only [List.length_append] at hl
    omega
  · rw [stretch_outside a p x hx]
    intro he
    apply hx
    rw [he]
    exact ⟨rfl,List.prefix_refl _⟩

theorem MiniBOccurrence.node_embedding_ne_upper {w : ℕ} {G : Garden w}
    {b c : GBranch G.tree} {m : MiniTreeCode} (h : MiniBOccurrence G b c m) (hG : G.IsPlain)
    (x : GNode (collapsePairedTreeGarden (h.isSubPairedTree hG)).tree) :
    collapsePairedTreeNodeEmbedding (h.isSubPairedTree hG) x ≠ b.toNode := by
  intro he
  have hv := congrArg (fun z : GNode G.tree => z.1) he
  change stretch b.1 (Comb.collapseDataOfDesc (h.isSubPairedTree hG).1).path x.1 = b.1 at hv
  rw [h.collapse_path hG] at hv
  exact stretch_ne_upper b.1 x.1 [m.c,m.lone] (by simp) hv

end WaveTurbulence.Reg.Skeleton
