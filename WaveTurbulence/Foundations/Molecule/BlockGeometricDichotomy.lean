/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.BlockGeometricData
public import WaveTurbulence.Foundations.Molecule.BlockChains
import Mathlib.Tactic

/-! # TARGET block_clcn: the exhaustive, exclusive geometric dichotomy -/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} (G : Garden w)

theorem cl_geometric_data {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) (hCL : CLParentPattern G S a b) :
    Nonempty (CLGeometricData G S a b) := by
  let D := clSpliceSlotsOfBlock hB hCL
  obtain ⟨pos,neg,hpn,hpos,hneg,hlabels⟩ := excluded_children_signed G b D.kept D.kept_ne_middle
  have hbottom (v : GNode G.tree) : (∀ i : Fin 3, i ≠ D.kept → ¬ (b.child i).IsDesc v) ↔
      ¬ (b.child pos).IsDesc v ∧ ¬ (b.child neg).IsDesc v := by
    constructor
    · intro h
      exact ⟨h pos ((hlabels pos).mpr (Or.inl rfl)),h neg ((hlabels neg).mpr (Or.inr rfl))⟩
    · rintro ⟨hp,hn⟩ i hi
      rcases (hlabels i).mp hi with rfl | rfl
      · exact hp
      · exact hn
  refine ⟨{ parentPattern := hCL
            excluded := D.excluded
            positive := pos
            negative := neg
            distinct := hpn
            excluded_sign := outer_child_sign G a D.excluded D.excluded_ne_middle
            positive_sign := hpos
            negative_sign := hneg
            lower_descendant := (cl_parent_strict_descendant G hB hCL).1
            lower_not_excluded := cl_excluded_child_no_descendant G hB hCL hB.2.1 hB.2.2.1
              D.excluded D.excluded_missing
            realization := ?_
            complete_pairing := incidence_complete_pairing G S }⟩
  intro v
  exact ((cl_node_realization_iff G hB hCL v).trans
    (cl_pruned_region_explicit G D.upper D.lower v)).trans
      (and_congr Iff.rfl (and_congr Iff.rfl (hbottom v)))

end WaveTurbulence.Mole
