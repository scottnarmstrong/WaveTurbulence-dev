/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RootWeightExpansion
public import WaveTurbulence.Foundations.Spine.DecoratedRootWeights
public import WaveTurbulence.Foundations.Spine.RootInputMultiplicity
/-! Exact root-weight expansion on an actual source decoration, retaining paired input identities. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem decoration_positiveRepresentative {w : ℕ} {V : Type*} [AddCommGroup V]
    (G : Garden w) (k : GNode G.tree → V) (hk : IsDecoration G k) (l : GLeaf G.tree) :
    k (positiveRepresentative G l).toNode = k l.toNode := by
  unfold positiveRepresentative
  split_ifs
  · rfl
  · exact (hk.2 l).symm

/-- Actual root descendants are the finite indices of the source sum rule. -/
abbrev RootLeafSlots {w : ℕ} (G : Garden w) (j : Fin w) :=
  {l : GLeaf G.tree // l ∈ (GNode.root G.tree j).leavesBelow}

theorem decorated_root_weight_expansion {w d : ℕ} (G : Garden w)
    (k : GNode G.tree → Mom d) (hk : IsDecoration G k) (j : Fin w) (m : ℕ) :
    jbr (k (GNode.root G.tree j)) ^ (2 * m) =
      ∑ choice : Fin m → RootQuadraticChoice (RootLeafSlots G j) d,
        ∏ a, rootQuadraticTerm
          (fun l : RootLeafSlots G j => nodeSign G.sig l.1.1)
          (fun l : RootLeafSlots G j => k (positiveRepresentative G l.1).toNode) (choice a) := by
  classical
  have he : (∑ l : RootLeafSlots G j,
      (nodeSign G.sig l.1.1 : ℤ) • k (positiveRepresentative G l.1).toNode) =
      (nodeSign G.sig (GNode.root G.tree j).1 : ℤ) • k (GNode.root G.tree j) := by
    simp_rw [decoration_positiveRepresentative G k hk]
    have hc := Finset.sum_coe_sort (GNode.root G.tree j).leavesBelow
      (fun l : GLeaf G.tree => (nodeSign G.sig l.1 : ℤ) • k l.toNode)
    exact hc.trans (sum_rule G.sig k hk.1 (GNode.root G.tree j)).symm
  have hh := jbr_sum_units_even_expansion
    (fun l : RootLeafSlots G j => nodeSign G.sig l.1.1)
    (fun l : RootLeafSlots G j => k (positiveRepresentative G l.1).toNode) m
  rw [he, jbr_units_smul] at hh
  exact hh

end WaveTurbulence.LGSpine
