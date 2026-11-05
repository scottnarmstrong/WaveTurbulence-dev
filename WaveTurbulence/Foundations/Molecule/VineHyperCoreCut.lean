/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionCuts
public import WaveTurbulence.Foundations.Molecule.VineHyperJointExclusion
public import WaveTurbulence.Foundations.Molecule.VineRealizationGroups
import Mathlib.Tactic

/-! # Every actual hyper-block subset induces a core cut of size at most two -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/-- Mapping the outer atom carrier preserves every induced bond cut sum. -/
theorem mapped_cutWeight_sum (M : Molecule V D) {A S : Finset V}
    (hAS : A ⊆ S) (f : V → ℕ) (hf : Set.InjOn f S) :
    (((M.groupBonds S).map (Sym2.map f)).map (cutWeight (A.image f))).sum=
      ((M.groupBonds S).map (cutWeight A)).sum := by
  rw [Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro e he
  obtain ⟨d,hd,rfl⟩ := Multiset.mem_map.mp he
  have hg := (mem_filter.mp (mem_val.mp hd)).2.2
  exact cutWeight_map_of_injOn hAS f hf hg.1 hg.2

/-- In an ordinary outer vine, every hyper-block subset has expanded cut
at most two. Full degree of nonjoint outer atoms ensures that no boundary
dart is lost by restricting to the outer vine. -/
theorem VineRealization.hyperBlock_expanded_cut_le_two (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S A : Finset V} {a b x y : V}
    (R : VineRealization M X S a b) (hS : M.IsBlock S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    rawCut (A.image R.f) (X.expand R.k).bonds ≤ 2 := by
  have hj := hyperBlock_outer_joints_absent M hS hH hAS
  have hclosed : ∀ d,M.atom d ∈ A → M.atom (M.mate d) ∈ S := by
    intro d hd
    have hda : M.atom d ≠ a := fun he => hj.1 (he ▸ hd)
    have hdb : M.atom d ≠ b := fun he => hj.2 (he ▸ hd)
    have hdeg := hS.2.2.2.2.2.2.2.2.1 _ (hAS hd) hda hdb
    exact Mole.full_degree_no_exit M hM (hS.1 (hAS hd)) hdeg rfl
  have he := mapped_cutWeight_sum M hAS R.f R.injOn
  rw [R.bonds_eq] at he
  have hraw : rawCut (A.image R.f) (X.expand R.k).bonds=
      ((M.groupBonds S).map (cutWeight A)).sum := by
    simpa only [rawCut,Multiset.map_coe,List.map_map,Function.comp_def,Multiset.sum_coe] using he
  rw [hraw,← boundary_card_eq_cutWeight M hAS hclosed]
  exact hyperBlock_boundary_card_le_two M hM hH

/-- TARGET subsetvc: an arbitrary-rung actual hyper-block subset yields
a finite-core cut of size at most two, with no cap or mask premise. -/
theorem VineRealization.hyperBlock_core_cut_le_two (M : Molecule V D) (hM : M.IsMolecule)
    {X : VineType} {S A : Finset V} {a b x y : V}
    (R : VineRealization M X S a b) (hS : M.IsBlock S a b)
    (hAS : A ⊆ S) (hH : Mole.IsHyperBlock M A x y) :
    rawCut (A.image R.f) X.template.bonds ≤ 2 :=
  (expand_rawCut_le _ X R.k R.length_eq).trans
    (R.hyperBlock_expanded_cut_le_two M hM hS hAS hH)

end WaveTurbulence.Vine
