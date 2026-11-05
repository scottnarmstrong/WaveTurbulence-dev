/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Splice

/-! # Disjoint half-edge splices commute, including cross-connected pairs -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem splice_outside {α : Type*} [DecidableEq α] (m : α → α) (a b x : α)
    (ha : x ≠ a) (hb : x ≠ b) :
    splice m a b x = if m x = a then m b else if m x = b then m a else m x := by
  rw [splice,ite_eq_right (not_or.mpr ⟨ha,hb⟩)]

theorem splice_unaffected {α : Type*} [DecidableEq α] (m : α → α) (a b x : α)
    (ha : x ≠ a) (hb : x ≠ b) (hma : m x ≠ a) (hmb : m x ≠ b) : splice m a b x = m x := by
  rw [splice_outside m a b x ha hb,ite_eq_right hma,ite_eq_right hmb]

/-- The only nontrivial commutation case: an outside port reaches the first
removed port. Its other partner may reach either of the second pair's ports. -/
theorem splice_commute_at_partner {α : Type*} [DecidableEq α] (m : α → α)
    (hm : Function.Involutive m) (a b c d x : α)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d) (hx : m x = a) :
    splice (splice m a b) c d x = splice (splice m c d) a b x := by
  let F := splice m a b
  let H := splice m c d
  have hF : F x = m b := by
    change splice m a b x = m b
    rw [splice_outside m a b x hxa hxb,ite_eq_left hx]
  have hH : H x = a := (splice_unaffected m c d x hxc hxd
    (by rw [hx]; exact hac) (by rw [hx]; exact had)).trans hx
  have hca : m c ≠ a := fun h => hxc (hm.injective (h.trans hx.symm)).symm
  have hda : m d ≠ a := fun h => hxd (hm.injective (h.trans hx.symm)).symm
  change splice F c d x = splice H a b x
  rw [splice_outside F c d x hxc hxd,splice_outside H a b x hxa hxb,hF,hH,ite_eq_left rfl]
  change (if m b = c then F d else if m b = d then F c else m b) = splice m c d b
  rw [splice_outside m c d b hbc hbd]
  by_cases hmc : m b = c
  · have hcb : m c = b := by have h := hm b; rw [hmc] at h; exact h
    have hdb : m d ≠ b := fun h => hcd (hm.injective (h.trans hcb.symm)).symm
    rw [ite_eq_left hmc,ite_eq_left hmc]
    exact splice_unaffected m a b d had.symm hbd.symm hda hdb
  · by_cases hmd : m b = d
    · have hdb : m d = b := by have h := hm b; rw [hmd] at h; exact h
      have hcb : m c ≠ b := fun h => hcd (hm.injective (h.trans hdb.symm))
      rw [ite_eq_right hmc,ite_eq_right hmc,ite_eq_left hmd,ite_eq_left hmd]
      exact splice_unaffected m a b c hac.symm hbc.symm hca hcb
    · rw [ite_eq_right hmc,ite_eq_right hmc,ite_eq_right hmd,ite_eq_right hmd]

/-- Literal half-edge splices at disjoint port pairs commute. This includes the
case of two cross-edges between the pairs, where both splices delete a closed loop. -/
theorem splice_commute {α : Type*} [DecidableEq α] (m : α → α)
    (hm : Function.Involutive m) (a b c d : α)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    splice (splice m a b) c d = splice (splice m c d) a b := by
  funext x
  by_cases hxa : x = a
  · subst x
    exact (splice_fixed (splice m a b) c d a (splice_left m a b)).trans (splice_left _ a b).symm
  by_cases hxb : x = b
  · subst x
    exact (splice_fixed (splice m a b) c d b (splice_right m a b)).trans (splice_right _ a b).symm
  by_cases hxc : x = c
  · subst x
    exact (splice_left _ c d).trans (splice_fixed (splice m c d) a b c (splice_left m c d)).symm
  by_cases hxd : x = d
  · subst x
    exact (splice_right _ c d).trans (splice_fixed (splice m c d) a b d (splice_right m c d)).symm
  by_cases hma : m x = a
  · exact splice_commute_at_partner m hm a b c d x hac had hbc hbd hcd hxa hxb hxc hxd hma
  by_cases hmb : m x = b
  · have h := splice_commute_at_partner m hm b a c d x hbc hbd hac had hcd hxb hxa hxc hxd hmb
    simpa only [splice_symm m b a,splice_symm (splice m c d) b a] using h
  by_cases hmc : m x = c
  · exact (splice_commute_at_partner m hm c d a b x hac.symm hbc.symm had.symm hbd.symm
      hab hxc hxd hxa hxb hmc).symm
  by_cases hmd : m x = d
  · have h := splice_commute_at_partner m hm d c a b x had.symm hbd.symm hac.symm hbc.symm
      hab hxd hxc hxa hxb hmd
    have he : splice (splice m c d) a b x = splice (splice m a b) c d x := by
      simpa only [splice_symm m d c,splice_symm (splice m a b) d c] using h
    exact he.symm
  simp [splice,hxa,hxb,hxc,hxd,hma,hmb,hmc,hmd]

end WaveTurbulence.Reg.Skeleton
