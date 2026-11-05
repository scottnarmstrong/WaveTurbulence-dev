/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBoundary
public import WaveTurbulence.Foundations.Molecule.MoleculeGroups
import Mathlib.Tactic

/-! # Gaps as actual signed joint flows (TARGET defdiff, subsetvc) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    [AddCommGroup E] [Module ℝ E] (M : Molecule V D)

/-- Signed flow within an induced atomic group at a specified atom. -/
@[expose] def groupFlow (S : Finset V) (k : D → E) (v : V) : E :=
  ∑ x ∈ (M.dartsAt v).filter (M.InGroup S), M.dartSign x • k x

/-- TARGET defdiff: the difference of the outgoing and incoming labels
within the group at its joint. This also applies to an adjoint block. -/
@[expose] def IsGroupGap (S : Finset V) (k : D → E) (v : V) (r : E) : Prop :=
  ∃ x y : D, M.atom x=v ∧ M.atom y=v ∧ M.InGroup S x ∧ M.InGroup S y ∧
    M.out x=true ∧ M.out y=false ∧ r=k x-k y

/-- At a degree-two joint, the gap equals the entire internal signed flow. -/
theorem groupGap_eq_flow {S : Finset V} {k : D → E} {v : V} {r : E}
    (hd : M.degIn S v=2) (hr : IsGroupGap M S k v r) : r=groupFlow M S k v := by
  obtain ⟨x,y,hx,hy,hgx,hgy,hox,hoy,rfl⟩ := hr
  have hne : x ≠ y := by intro h; have hh := h ▸ hox; rw [hoy] at hh; cases hh
  let T := (M.dartsAt v).filter (M.InGroup S)
  have hxT : x ∈ T := mem_filter.mpr ⟨(Mole.mem_dartsAt M v x).mpr hx,hgx⟩
  have hyT : y ∈ T := mem_filter.mpr ⟨(Mole.mem_dartsAt M v y).mpr hy,hgy⟩
  have hsub : ({x,y} : Finset D) ⊆ T := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hxT
    · have he := mem_singleton.mp hz
      subst z
      exact hyT
  have he : ({x,y} : Finset D)=T := eq_of_subset_of_card_le hsub (by
    rw [card_pair hne]
    exact hd.le)
  change _=∑ z ∈ T, M.dartSign z • k z
  rw [← he,sum_pair hne]
  simp only [Molecule.dartSign,hox,hoy,Bool.false_eq_true,ite_false,ite_true,
    neg_smul,one_smul,sub_eq_add_neg]

/-- The block gap at either joint is unique. -/
theorem blockGap_unique {S : Finset V} {a b : V} {k : D → E} {r r' : E}
    (hB : M.IsBlock S a b) (hr : IsGroupGap M S k a r) (hr' : IsGroupGap M S k a r') : r=r' :=
  (groupGap_eq_flow M (Mole.block_joint_degrees M hB).1 hr).trans
    (groupGap_eq_flow M (Mole.block_joint_degrees M hB).1 hr').symm

end WaveTurbulence.Vine
