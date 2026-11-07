/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CurrentBlocks
public import WaveTurbulence.Foundations.Molecule.CLSpliceGarden

/-! # Actual CL regions from the current connected block predicate -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree

/-- The source joint/child labels, with their actual internal-slot witnesses.
This is derived from a current connected CL block; no realization is assumed. -/
structure CLRegionData {w : ℕ} (G : Garden w) (S : Finset (GBranch G.tree))
    (a b : GBranch G.tree) extends Mole.CLSpliceSlots G S a b where
  parentPattern : Mole.CLParentPattern G S a b
  positive : Fin 3
  negative : Fin 3
  distinct : positive ≠ negative
  positive_sign : G.sign (b.child positive) = 1
  negative_sign : G.sign (b.child negative) = -1
  lower_excluded : ∀ i : Fin 3, i ≠ kept ↔ i = positive ∨ i = negative

noncomputable def clRegionData {w : ℕ} (G : Garden w) {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hB : G.molecule.IsBlock S a b)
    (hCL : Mole.CLParentPattern G S a b) : CLRegionData G S a b := by
  apply Classical.choice
  let D := Mole.clSpliceSlotsOfBlock hB hCL
  obtain ⟨p,n,hpn,hp,hn,he⟩ := Mole.excluded_children_signed G b D.kept D.kept_ne_middle
  exact ⟨{ toCLSpliceSlots := D
           parentPattern := hCL
           positive := p
           negative := n
           distinct := hpn
           positive_sign := hp
           negative_sign := hn
           lower_excluded := he }⟩

/-- The chosen slot labels realize exactly the actual source incidence region. -/
noncomputable def CLRegionData.geometry {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (D : CLRegionData G S a b) (hB : G.molecule.IsBlock S a b) :
    Mole.CLGeometricData G S a b := by
  have hdeg := hB
  have hbottom (v : GNode G.tree) : (∀ i : Fin 3, i ≠ D.kept → ¬ (b.child i).IsDesc v) ↔
      ¬ (b.child D.positive).IsDesc v ∧ ¬ (b.child D.negative).IsDesc v := by
    constructor
    · intro h
      exact ⟨h D.positive ((D.lower_excluded _).mpr (Or.inl rfl)),
        h D.negative ((D.lower_excluded _).mpr (Or.inr rfl))⟩
    · rintro ⟨hp,hn⟩ i hi
      rcases (D.lower_excluded i).mp hi with rfl | rfl
      · exact hp
      · exact hn
  refine {
    parentPattern := D.parentPattern
    excluded := D.excluded
    positive := D.positive
    negative := D.negative
    distinct := D.distinct
    excluded_sign := Mole.outer_child_sign G a D.excluded D.excluded_ne_middle
    positive_sign := D.positive_sign
    negative_sign := D.negative_sign
    lower_descendant := (Mole.cl_parent_strict_descendant G hdeg D.parentPattern).1
    lower_not_excluded := Mole.cl_excluded_child_no_descendant G hdeg D.parentPattern hdeg.2.1 hdeg.2.2.1
      D.excluded D.excluded_missing
    realization := ?_
    complete_pairing := Mole.incidence_complete_pairing G S }
  intro v
  exact ((Mole.cl_node_realization_iff G hdeg D.parentPattern v).trans
    (Mole.cl_pruned_region_explicit G D.upper D.lower v)).trans
      (and_congr Iff.rfl (and_congr Iff.rfl (hbottom v)))

end WaveTurbulence.RegRed
