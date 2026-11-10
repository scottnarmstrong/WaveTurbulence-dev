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

end WaveTurbulence.RegRed
