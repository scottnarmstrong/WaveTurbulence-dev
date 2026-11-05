/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLBoundaryRoots
public import WaveTurbulence.Foundations.Molecule.SpliceSignedLeaves
import Mathlib.Tactic

/-! # Signed boundary assignment and retained-leaf pairing for actual CL blocks
TARGET `block_clcn` (2). Boundary roots and pairing closure are derived
from the garden block, rather than assumed as surgery hypotheses.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b)
variable (e k : Fin 3) (he : e.succ ∉ internalPositions G S a) (he1 : e ≠ 1)

theorem clSignedBoundary_sign (hk1 : k ≠ 1) (i : Fin 3) :
    G.sign ((clSignedBoundaryRoots hB hCL e k he he1).node i) = G.sign (a.child i) := by
  classical
  change G.sign (clBaseBoundary a b e k
    (clBoundarySelector e (clSameSign a b) i)) = G.sign (a.child i)
  have hec : e = 0 ∨ e = 2 := by fin_cases e <;> simp_all
  have hkc : k = 0 ∨ k = 2 := by fin_cases k <;> simp_all
  rcases hec with rfl | rfl <;> rcases hkc with rfl | rfl <;>
    rcases Int.units_eq_one_or (G.sign a.toNode) with ha | ha <;>
    rcases Int.units_eq_one_or (G.sign b.toNode) with hb | hb <;>
    fin_cases i <;> simp [clBaseBoundary,clBoundarySelector,clSameSign,otherOuterChild,child_sign_formula,ha,hb]

theorem clSignedBoundary_descendant_union (v : GNode G.tree) :
    (∃ i, ((clSignedBoundaryRoots hB hCL e k he he1).node i).IsDesc v) ↔
      (a.child e).IsDesc v ∨ (b.child 1).IsDesc v ∨ (b.child (otherOuterChild k)).IsDesc v := by
  classical
  change (∃ i, (clBaseBoundary a b e k
    (clBoundarySelector e (clSameSign a b) i)).IsDesc v) ↔ _
  have hp := clBoundarySelector_bijective e he1 (clSameSign a b)
  have hf : (∃ i, (clBaseBoundary a b e k
      (clBoundarySelector e (clSameSign a b) i)).IsDesc v) ↔
      ∃ j, (clBaseBoundary a b e k j).IsDesc v := by
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨_,hi⟩
    · rintro ⟨j,hj⟩
      obtain ⟨i,rfl⟩ := hp.2 j
      exact ⟨i,hj⟩
  rw [hf]
  constructor
  · rintro ⟨j,hj⟩
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr hj)
  · rintro (hj | hj | hj)
    · exact ⟨0,hj⟩
    · exact ⟨1,hj⟩
    · exact ⟨2,hj⟩

end WaveTurbulence.Mole
