/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceSpec
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): bonds between unmerged atoms are unchanged by a splice

Answers the "triple-bond clause" question of `SubproChoices.Structural`: a triple bond of the spliced
garden between two atoms that are not hinge (crown) atoms is a triple bond of the skeleton garden.
So, once `M(G_sk)` has no triple bond (TARGET L709, `skeleton`), every triple bond of `M(G_sb)` has a hinge
endpoint (DH23 L1741 (c)).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {w : ℕ} {G0 G : Garden w} {cls : GBranch G0.tree → Option (GBranch G0.tree)}

theorem repC_eq_iff_of_unmerged (hcls : ClsOK cls) {v w' : GBranch G0.tree} (hv : cls v = none) :
    repC cls w' = v ↔ w' = v := by
  constructor
  · intro h
    unfold repC at h
    cases hw : cls w' with
    | none => rw [hw] at h; simpa using h
    | some a' =>
      rw [hw] at h
      have h2 := hcls w' a' hw
      have : a' = v := by simpa using h
      rw [this, hv] at h2; simp at h2
  · rintro rfl; unfold repC; rw [hv]; rfl

theorem mem_bonds_iff' {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (x : D) :
    x ∈ M.bonds ↔ M.out x = true := by simp [Molecule.bonds]

theorem SpMap.bondsBetween_eq (M : SpMap G0 G cls) (hcls : ClsOK cls) {a b : GBranch G.tree}
    (ha : cls (M.ob a) = none) (hb : cls (M.ob b) = none) :
    G.molecule.bondsBetween a b = G0.molecule.bondsBetween (M.ob a) (M.ob b) := by
  classical
  unfold Molecule.bondsBetween
  apply Finset.card_bij (fun y _ => M.od y)
  · intro y hy
    rw [Finset.mem_filter, mem_bonds_iff'] at hy ⊢
    unfold Molecule.ends at hy ⊢
    obtain ⟨h1, h2⟩ := hy
    refine ⟨by rw [M.od_out]; exact h1, ?_⟩
    have e1 := M.ob_atom y
    have e2 := M.ob_atom (G.molecule.mate y)
    rw [M.od_mate] at e2
    rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h3] at e1; rw [h4] at e2
      rw [(repC_eq_iff_of_unmerged hcls ha).mp e1.symm, (repC_eq_iff_of_unmerged hcls hb).mp e2.symm]
    · rw [h3] at e1; rw [h4] at e2
      rw [(repC_eq_iff_of_unmerged hcls hb).mp e1.symm, (repC_eq_iff_of_unmerged hcls ha).mp e2.symm,
        Sym2.eq_swap]
  · intro x y _ _ h; exact M.od_inj h
  · intro x hx
    rw [Finset.mem_filter, mem_bonds_iff'] at hx
    unfold Molecule.ends at hx
    obtain ⟨h1, h2⟩ := hx
    have hnot : ¬∃ a2, cls (G0.molecule.atom x) = some a2 ∧ cls (G0.molecule.atom (G0.molecule.mate x)) = some a2 := by
      rintro ⟨a2, e1, e2⟩
      rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [h3, ha] at e1; simp at e1
      · rw [h3, hb] at e1; simp at e1
    obtain ⟨y, hy⟩ := (M.od_range x).mpr hnot
    refine ⟨y, ?_, hy⟩
    rw [Finset.mem_filter, mem_bonds_iff']
    unfold Molecule.ends
    refine ⟨by rw [← M.od_out, hy]; exact h1, ?_⟩
    have e1 := M.ob_atom y
    have e2 := M.ob_atom (G.molecule.mate y)
    rw [M.od_mate, hy] at e2
    rw [hy] at e1
    rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · have u1 : G.molecule.atom y = a := M.ob_inj (by rw [e1, h3]; exact (repC_eq_iff_of_unmerged hcls ha).mpr rfl)
      have u2 : G.molecule.atom (G.molecule.mate y) = b := M.ob_inj (by rw [e2, h4]; exact (repC_eq_iff_of_unmerged hcls hb).mpr rfl)
      rw [u1, u2]
    · have u1 : G.molecule.atom y = b := M.ob_inj (by rw [e1, h3]; exact (repC_eq_iff_of_unmerged hcls hb).mpr rfl)
      have u2 : G.molecule.atom (G.molecule.mate y) = a := M.ob_inj (by rw [e2, h4]; exact (repC_eq_iff_of_unmerged hcls ha).mpr rfl)
      rw [u1, u2, Sym2.eq_swap]

end WaveTurbulence.RedSplice
