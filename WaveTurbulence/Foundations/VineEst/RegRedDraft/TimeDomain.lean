/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.RegRedDraft.Clocks

/-! # Source time inequalities in original parent-clock coordinates -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Reg.Skeleton

theorem branch_eq_child_of_isChildOf {w : ℕ} {tree : Fin w → TTree}
    {c b : GBranch tree} (h : c.IsChildOf b) : ∃ i : Fin 3, c.toNode = b.child i := by
  obtain ⟨hi,i,hp⟩ := h
  exact ⟨i,Subtype.ext (Prod.ext hi hp)⟩

theorem not_loneParent_of_plain {w : ℕ} (G : Garden w) (hG : G.IsPlain)
    (b : GBranch G.tree) : ¬ G.IsLoneParent b := by
  rintro ⟨ℓ,hℓ,hb⟩
  have hm := hG ℓ
  change G.mark ℓ = some .lower at hℓ
  rw [hℓ] at hm
  contradiction

/-- For an ordinary layered garden, the literal all-node upper bound and child
inequalities are equivalent to the original-parent clock inequalities. -/
theorem kDomain_eq_coreTimeDomain {w : ℕ} (LG : LayeredGarden w)
    (hG : LG.garden.IsPlain) (top s : ℝ) :
    kDomain LG (fun _ => top) s = coreTimeDomain (fun b => LG.layer b.toNode) top := by
  ext τ
  constructor
  · intro h b
    refine ⟨(h b).1,(h b).2.1,(h b).2.2.1,?_⟩
    by_cases hb : b.1.2 = []
    · have he : b.toNode = GNode.root LG.garden.tree b.1.1 := Subtype.ext (Prod.ext rfl hb)
      rw [he,parentClock_root]
      exact (h b).2.2.2.1
    · have hc : b.IsChildOf (b.toNode.parent hb) := by
        refine ⟨rfl,b.1.2.getLast hb,?_⟩
        exact (List.dropLast_append_getLast hb).symm
      change τ b < parentClock top τ b.toNode
      rw [parentClock_nonroot top τ b.toNode hb]
      exact (h (b.toNode.parent hb)).2.2.2.2.1 b hc
  · intro h b
    refine ⟨(h b).1,(h b).2.1,(h b).2.2.1,
      lt_top_of_lt_parentClock top τ (fun b => (h b).2.2.2) b,?_,?_⟩
    · intro c hc
      obtain ⟨i,hi⟩ := branch_eq_child_of_isChildOf hc
      have ht := (h c).2.2.2
      rw [hi,parentClock_child] at ht
      exact ht
    · intro hl
      exact (not_loneParent_of_plain LG.garden hG b hl).elim

end WaveTurbulence.RegRed
