/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniARecovery
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.MiniBRecovery

/-! # Actual source minis give the exact three prescribed graph bonds -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- Actual paired child leaves give a child-to-child bond in the port graph. -/
theorem LeafBond.portMate {w : ℕ} {G : Garden w} {b c : GBranch G.tree} {i j : Fin 3}
    (h : LeafBond G b c i j) : portMate G (.inr (b,i.succ)) = .inr (c,j.succ) := by
  obtain ⟨ℓ,q,hℓ,hq,hp⟩ := h
  rw [← encodeIncidence_child G b i,← encodeIncidence_child G c j,← hℓ,← hq,
    portMate_encode,incidenceMate_leaf,hp]

/-- The exact A source mini defines a dipole with its two parent ports free. -/
@[expose] noncomputable def MiniAOccurrence.branchDipole {w : ℕ} {G : Garden w}
    {b c : GBranch G.tree} {k : MiniCplCode} (h : MiniAOccurrence G b c k) (hG : G.IsPlain) :
    BranchDipole G where
  u := b
  v := c
  ne := by
    intro he
    have ha := incomparable_addr_ne (Comb.subCouple_incomparable (h.isSubCouple hG))
    exact ha (congrArg (fun x : GBranch G.tree => x.1) he)
  perm := miniAPerm k
  free := 0
  internal := by
    intro i hi
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    change portMate G (.inr (b,j.succ)) = .inr (c,(k.partner j).succ)
    exact (h.2 j).portMate

/-- The exact B source mini defines its continuing bond and the red/green pair bonds. -/
@[expose] noncomputable def MiniBOccurrence.branchDipole {w : ℕ} {G : Garden w}
    {b c : GBranch G.tree} {m : MiniTreeCode} (h : MiniBOccurrence G b c m) : BranchDipole G where
  u := b
  v := c
  ne := by
    intro he
    have hv := congrArg (fun a : GNode G.tree => a.1.2.length) h.1
    have he' := congrArg (fun a : GBranch G.tree => a.1.2.length) he
    change (b.1.2 ++ [m.c]).length = c.1.2.length at hv
    simp only [List.length_append,List.length_singleton] at hv
    omega
  perm := miniBPerm m
  free := 0
  internal := by
    intro i hi
    obtain ⟨j,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hi
    by_cases hj : j = m.c
    · subst j
      rw [miniBPerm_continuing]
      exact (portMate_child_parent_iff G b c m.c).mpr h.1
    · rcases miniTree_front_slots_cover m j hj with rfl | rfl
      · rw [miniBPerm_red]
        exact h.2.1.portMate
      · rw [miniBPerm_green]
        exact h.2.2.portMate

end WaveTurbulence.Reg.Skeleton
