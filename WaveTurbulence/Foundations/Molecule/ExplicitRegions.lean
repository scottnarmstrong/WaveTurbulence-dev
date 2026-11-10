/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.CLLeafRealization
public import WaveTurbulence.Foundations.Molecule.JointChildSlots
import Mathlib.Tactic

/-! # Source descendant formulas from the actual joint slots
TARGET `block_clcn`: three excluded child subtrees for CL, and one
excluded child subtree at each joint for CN.
-/

public section
namespace WaveTurbulence.Mole
open TTree Finset
variable {w : ℕ} (G : Garden w)

theorem cl_pruned_region_explicit {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {excluded kept : Fin 3}
    (ha : ∀ i : Fin 3, i.succ ∈ internalPositions G S a ↔ i ≠ excluded)
    (hb : ∀ i : Fin 3, i.succ ∈ internalPositions G S b ↔ i = kept)
    (v : GNode G.tree) :
    InCLPrunedRegion G S a b v ↔
      a.toNode.IsDesc v ∧ ¬ (a.child excluded).IsDesc v ∧
        ∀ i : Fin 3, i ≠ kept → ¬ (b.child i).IsDesc v := by
  constructor
  · intro hv
    refine ⟨hv.1,hv.2 a (by simp) excluded ?_,?_⟩
    · exact fun h => (ha excluded).mp h rfl
    · intro i hi
      exact hv.2 b (by simp) i (fun h => hi ((hb i).mp h))
  · rintro ⟨hd,haDesc,hbDesc⟩
    refine ⟨hd,?_⟩
    intro j hj i hi
    simp only [mem_insert,mem_singleton] at hj
    rcases hj with he | he
    · subst j
      have heq : i = excluded := by
        by_contra hn
        exact hi ((ha i).mpr hn)
      exact heq ▸ haDesc
    · subst j
      exact hbDesc i (fun he => hi ((hb i).mpr he))

end WaveTurbulence.Mole
