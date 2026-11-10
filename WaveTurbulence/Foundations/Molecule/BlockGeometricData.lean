/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLSpliceMoleculeIso
import Mathlib.Tactic

/-! # Source-shaped CL and CN geometric alternatives
TARGET `block_clcn` (1), with the lower CL excluded children explicitly
labelled by signs + and −. The realization is tied to the literal atom
set through the proved incidence realization, not a free geometric set.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} (G : Garden w)

theorem excluded_children_signed (b : GBranch G.tree) (kept : Fin 3) (hk : kept ≠ 1) :
    ∃ pos neg : Fin 3, pos ≠ neg ∧ G.sign (b.child pos) = 1 ∧ G.sign (b.child neg) = -1 ∧
      ∀ i : Fin 3, i ≠ kept ↔ i = pos ∨ i = neg := by
  have hc : kept = 0 ∨ kept = 2 := by fin_cases kept <;> simp_all
  rcases hc with rfl | rfl
  · rcases Int.units_eq_one_or (G.sign b.toNode) with hs | hs
    · refine ⟨2,1,by decide,?_,?_,by decide⟩ <;> simp [child_sign_formula,hs]
    · refine ⟨1,2,by decide,?_,?_,by decide⟩ <;> simp [child_sign_formula,hs]
  · rcases Int.units_eq_one_or (G.sign b.toNode) with hs | hs
    · refine ⟨0,1,by decide,?_,?_,by decide⟩ <;> simp [child_sign_formula,hs]
    · refine ⟨1,0,by decide,?_,?_,by decide⟩ <;> simp [child_sign_formula,hs]

structure CLGeometricData (S : Finset (GBranch G.tree)) (upper lower : GBranch G.tree) where
  parentPattern : CLParentPattern G S upper lower
  excluded : Fin 3
  positive : Fin 3
  negative : Fin 3
  distinct : positive ≠ negative
  excluded_sign : G.sign (upper.child excluded) = G.sign upper.toNode
  positive_sign : G.sign (lower.child positive) = 1
  negative_sign : G.sign (lower.child negative) = -1
  lower_descendant : upper.toNode.IsDesc lower.toNode
  lower_not_excluded : ¬ (upper.child excluded).IsDesc lower.toNode
  realization : ∀ v : GNode G.tree, InIncidenceRealization G S v ↔
    upper.toNode.IsDesc v ∧ ¬ (upper.child excluded).IsDesc v ∧
      ¬ (lower.child positive).IsDesc v ∧ ¬ (lower.child negative).IsDesc v
  complete_pairing : ∀ l : GLeaf G.tree, InIncidenceRealization G S l.toNode →
    G.mark l = none ∧ InIncidenceRealization G S (G.pair l).toNode

theorem incidence_complete_pairing (S : Finset (GBranch G.tree)) (l : GLeaf G.tree)
    (hl : InIncidenceRealization G S l.toNode) :
    G.mark l = none ∧ InIncidenceRealization G S (G.pair l).toNode := by
  have hi := (leaf_incidence_realization_iff G S l).mp hl
  exact ⟨internal_leaf_unmarked G hi,(incidence_realization_leaf_pair G S l).mpr hl⟩

end WaveTurbulence.Mole
