/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceObj2
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), B: internal parents of the residual vine

For a VC group (decomposition in the garden molecule itself) the internal-parent flags at the two joints of
the skipped vine are the same before and after the splice (`ip_x`, `ip_y`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree

variable {w : ℕ} {G0 G : Garden w} {cls : GBranch G0.tree → Option (GBranch G0.tree)}

/-- The PC dart at a non-root branching node, at the child end. -/
@[expose] def pcDart (G : Garden w) (x : GBranch G.tree) (hx : x.1.2 ≠ []) : GardenDart G :=
  Sum.inl (⟨x, hx⟩, false)

theorem pcDart_atom (x : GBranch G0.tree) (hx : x.1.2 ≠ []) : G0.molecule.atom (pcDart G0 x hx) = x := rfl

theorem pcDart_mate_atom (x : GBranch G0.tree) (hx : x.1.2 ≠ []) :
    G0.molecule.atom (G0.molecule.mate (pcDart G0 x hx)) = GNode.parent x.toNode hx := rfl

section ip
variable {S A L0 R0 : Finset (GBranch G0.tree)} {a b x y : GBranch G0.tree}
  (H : SDecomp G0.molecule cls S A L0 R0 a b x y) (M : SpMap G0 G cls) (hc : ClsOK cls)
  (hup : L0 ≠ ∅ → ((cls x).getD x = x ∧ ¬ InternalParent G0 L0 x) ∨
    ((cls x).getD x = a ∧ ¬ InternalParent G0 L0 a ∧ InternalParent G0 L0 x))
include H hup

theorem ip_x_fwd (hip : InternalParent G (A.image (M.pi hc)) (M.pi hc x)) : InternalParent G0 A x := by
  obtain ⟨hn, hp⟩ := hip
  obtain ⟨v, hv, hpv⟩ := Finset.mem_image.mp hp
  have hobx : M.ob (M.pi hc x) = (cls x).getD x := M.ob_pi hc x
  have ho : (M.ob (M.pi hc x)).1.2 ≠ [] := fun h => hn ((M.ob_root _).mp h)
  have hpar := M.ob_parent (M.pi hc x) hn ho
  have hrv : (cls v).getD v = repC cls (GNode.parent (M.ob (M.pi hc x)).toNode ho) := by
    rw [← hpar, ← hpv, M.ob_pi hc v]; rfl
  by_cases hr : (cls x).getD x = x
  · -- the crown is `x` itself
    have hx0 : x.1.2 ≠ [] := by rw [hobx, hr] at ho; exact ho
    refine ⟨hx0, ?_⟩
    have hpar' : GNode.parent (M.ob (M.pi hc x)).toNode ho = GNode.parent x.toNode hx0 := by
      congr 1 <;> simp [hobx, hr]
    rw [hpar'] at hrv
    rcases H.class_of (GNode.parent x.toNode hx0) v hv hrv.symm with h | h | h
    · -- parent x ∈ L0
      exfalso
      have hL : L0 ≠ ∅ := fun h0 => by rw [h0] at h; simp at h
      rcases hup hL with ⟨_, hn⟩ | ⟨h2, _, _⟩
      · exact hn ⟨hx0, h⟩
      · have : x = a := hr.symm.trans h2
        rcases H.hL with ⟨h0, _⟩ | ⟨hxa, _, _⟩
        · exact hL h0
        · exact hxa this
    · -- parent x ∈ R0 : an S-internal non-class-internal dart at x
      have hxS : x ∈ S := H.hAsub H.hxA
      have hS : G0.molecule.InGroup S (pcDart G0 x hx0) := ⟨hxS, H.hRsub h⟩
      have hnc : ¬ ∃ r', cls (G0.molecule.atom (pcDart G0 x hx0)) = some r' ∧
          cls (G0.molecule.atom (G0.molecule.mate (pcDart G0 x hx0))) = some r' := by
        rintro ⟨r', h1, h2⟩
        rw [pcDart_atom] at h1
        rw [pcDart_mate_atom] at h2
        have hR : R0 ≠ ∅ := fun h0 => by rw [h0] at h; simp at h
        have hxL : x ∈ L0 := by
          by_contra hxL
          have hxR : x ∉ R0 := by
            intro hxR
            rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hi⟩
            · exact hR h0
            · have : x ∈ R0 ∩ A := mem_inter.mpr ⟨hxR, H.hxA⟩
              rw [hi, mem_singleton] at this
              exact H.hxy this
          have := H.hNone x hxS hxL hxR
          rw [this] at h1; cases h1
        have heq : (cls (GNode.parent x.toNode hx0)).getD (GNode.parent x.toNode hx0) = (cls x).getD x := by
          rw [h1, h2]; rfl
        have hpL := H.hLcl _ x hxL heq
        exact Finset.disjoint_left.mp H.hd hpL h
      have hAi := H.Aint hS hnc (by rw [pcDart_atom]; exact H.hxA)
      exact hAi.2
    · exact h ▸ hv
  · -- the crown is `a`
    have hxL : x ∈ L0 := by
      by_contra hxL
      have hxR : x ∉ R0 := by
        intro hxR
        rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hi⟩
        · rw [h0] at hxR; simp at hxR
        · have : x ∈ R0 ∩ A := mem_inter.mpr ⟨hxR, H.hxA⟩
          rw [hi, mem_singleton] at this
          exact H.hxy this
      have := H.hNone x (H.hAsub H.hxA) hxL hxR
      exact hr (by rw [this]; rfl)
    have hL : L0 ≠ ∅ := fun h0 => by rw [h0] at hxL; simp at hxL
    rcases hup hL with ⟨h1, _⟩ | ⟨h1, hnpa, _⟩
    · exact absurd h1 hr
    · exfalso
      -- parent of the crown `a`
      have ha0 : a.1.2 ≠ [] := by rw [hobx, h1] at ho; exact ho
      have hpar' : GNode.parent (M.ob (M.pi hc x)).toNode ho = GNode.parent a.toNode ha0 := by
        congr 1 <;> simp [hobx, h1]
      rw [hpar'] at hrv
      obtain ⟨hxa, hLB, hi⟩ : x ≠ a ∧ G0.molecule.IsBlock L0 a x ∧ L0 ∩ A = {x} := by
        rcases H.hL with ⟨h0, _⟩ | h
        · exact absurd h0 hL
        · exact h
      have haL : a ∈ L0 := hLB.2.1
      have hpaL : GNode.parent a.toNode ha0 ∉ L0 := fun h => hnpa ⟨ha0, h⟩
      have haS : a ∈ S := H.hLsub haL
      rcases H.class_of (GNode.parent a.toNode ha0) v hv hrv.symm with h | h | h
      · exact hpaL h
      · -- parent a ∈ R0
        have hS : G0.molecule.InGroup S (pcDart G0 a ha0) := ⟨haS, H.hRsub h⟩
        have hnc : ¬ ∃ r', cls (G0.molecule.atom (pcDart G0 a ha0)) = some r' ∧
            cls (G0.molecule.atom (G0.molecule.mate (pcDart G0 a ha0))) = some r' := by
          rintro ⟨r', h1', h2'⟩
          rw [pcDart_atom] at h1'
          rw [pcDart_mate_atom] at h2'
          have heq : (cls (GNode.parent a.toNode ha0)).getD (GNode.parent a.toNode ha0) = (cls a).getD a := by
            rw [h1', h2']; rfl
          exact hpaL (H.hLcl _ a haL heq)
        have := H.notL hS hnc (by rw [pcDart_atom]; exact haL)
        rw [pcDart_atom] at this
        have : a ∈ L0 ∩ A := mem_inter.mpr ⟨haL, this⟩
        rw [hi, mem_singleton] at this
        exact hxa this.symm
      · -- parent a = v ∈ A
        have hpA : GNode.parent a.toNode ha0 ∈ A := h ▸ hv
        have hS : G0.molecule.InGroup S (pcDart G0 a ha0) := ⟨haS, H.hAsub hpA⟩
        have hnc : ¬ ∃ r', cls (G0.molecule.atom (pcDart G0 a ha0)) = some r' ∧
            cls (G0.molecule.atom (G0.molecule.mate (pcDart G0 a ha0))) = some r' := by
          rintro ⟨r', h1', h2'⟩
          rw [pcDart_atom] at h1'
          rw [pcDart_mate_atom] at h2'
          have heq : (cls (GNode.parent a.toNode ha0)).getD (GNode.parent a.toNode ha0) = (cls a).getD a := by
            rw [h1', h2']; rfl
          exact hpaL (H.hLcl _ a haL heq)
        have := H.notL hS hnc (by rw [pcDart_atom]; exact haL)
        rw [pcDart_atom] at this
        have : a ∈ L0 ∩ A := mem_inter.mpr ⟨haL, this⟩
        rw [hi, mem_singleton] at this
        exact hxa this.symm

theorem ip_x_bwd (hip : InternalParent G0 A x) : InternalParent G (A.image (M.pi hc)) (M.pi hc x) := by
  obtain ⟨hx0, hpA⟩ := hip
  have hobx : M.ob (M.pi hc x) = (cls x).getD x := M.ob_pi hc x
  by_cases hr : (cls x).getD x = x
  · have ho : (M.ob (M.pi hc x)).1.2 ≠ [] := by rw [hobx, hr]; exact hx0
    have hn : (M.pi hc x).1.2 ≠ [] := fun h => ho ((M.ob_root _).mpr h)
    refine ⟨hn, Finset.mem_image.mpr ⟨_, hpA, ?_⟩⟩
    apply M.ob_inj
    rw [M.ob_pi hc, M.ob_parent (M.pi hc x) hn ho]
    have hpar' : GNode.parent (M.ob (M.pi hc x)).toNode ho = GNode.parent x.toNode hx0 := by
      congr 1 <;> simp [hobx, hr]
    rw [hpar']
  · exfalso
    have hxL : x ∈ L0 := by
      by_contra hxL
      have hxR : x ∉ R0 := by
        intro hxR
        rcases H.hR with ⟨h0, _⟩ | ⟨_, _, hi⟩
        · rw [h0] at hxR; simp at hxR
        · have : x ∈ R0 ∩ A := mem_inter.mpr ⟨hxR, H.hxA⟩
          rw [hi, mem_singleton] at this
          exact H.hxy this
      have := H.hNone x (H.hAsub H.hxA) hxL hxR
      exact hr (by rw [this]; rfl)
    have hL : L0 ≠ ∅ := fun h0 => by rw [h0] at hxL; simp at hxL
    rcases hup hL with ⟨h1, _⟩ | ⟨_, _, hipx⟩
    · exact hr h1
    · obtain ⟨hxa, hLB, hi⟩ : x ≠ a ∧ G0.molecule.IsBlock L0 a x ∧ L0 ∩ A = {x} := by
        rcases H.hL with ⟨h0, _⟩ | h
        · exact absurd h0 hL
        · exact h
      obtain ⟨_, hpL⟩ := hipx
      have : GNode.parent x.toNode hx0 ∈ L0 ∩ A := mem_inter.mpr ⟨hpL, hpA⟩
      rw [hi, mem_singleton] at this
      exact parent_ne_self x hx0 this

theorem ip_x : InternalParent G (A.image (M.pi hc)) (M.pi hc x) ↔ InternalParent G0 A x :=
  ⟨ip_x_fwd H M hc hup, ip_x_bwd H M hc hup⟩

end ip

theorem ip_y {S A L0 R0 : Finset (GBranch G0.tree)} {a b x y : GBranch G0.tree}
    (H : SDecomp G0.molecule cls S A L0 R0 a b x y) (M : SpMap G0 G cls) (hc : ClsOK cls)
    (hup : R0 ≠ ∅ → ((cls y).getD y = y ∧ ¬ InternalParent G0 R0 y) ∨
      ((cls y).getD y = b ∧ ¬ InternalParent G0 R0 b ∧ InternalParent G0 R0 y)) :
    InternalParent G (A.image (M.pi hc)) (M.pi hc y) ↔ InternalParent G0 A y :=
  ip_x H.symm M hc hup

end WaveTurbulence.RedSplice
