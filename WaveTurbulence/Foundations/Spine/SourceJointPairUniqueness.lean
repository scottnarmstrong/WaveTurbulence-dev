/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceBlockJointGaps
/-! The actual outgoing/incoming pair at a block joint is unique and respects nested blocks. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

abbrev SourceJointPair {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)
    (S : Finset V) (v : V) (x y : D) : Prop :=
  M.atom x = v ∧ M.atom y = v ∧ M.InGroup S x ∧ M.InGroup S y ∧
    M.out x = true ∧ M.out y = false

theorem source_joint_pair_unique {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] (M : Molecule V D) {S : Finset V} {a b v : V}
    (hB : M.IsBlock S a b) (hv : v = a ∨ v = b) {x y x' y' : D}
    (hxy : SourceJointPair M S v x y) (hxy' : SourceJointPair M S v x' y') : x = x' ∧ y = y' := by
  classical
  have hout : M.outIn S v = 1 := hv.elim (fun h => h ▸ hB.2.2.2.2.1)
    (fun h => h ▸ hB.2.2.2.2.2.2.1)
  have hin : M.inIn S v = 1 := hv.elim (fun h => h ▸ hB.2.2.2.2.2.1)
    (fun h => h ▸ hB.2.2.2.2.2.2.2.1)
  constructor
  · exact Finset.card_le_one.mp hout.le x (mem_filter.mpr
      ⟨(Mole.mem_dartsAt M v x).mpr hxy.1, hxy.2.2.1, hxy.2.2.2.2.1⟩) x'
      (mem_filter.mpr ⟨(Mole.mem_dartsAt M v x').mpr hxy'.1, hxy'.2.2.1, hxy'.2.2.2.2.1⟩)
  · exact Finset.card_le_one.mp hin.le y (mem_filter.mpr
      ⟨(Mole.mem_dartsAt M v y).mpr hxy.2.1, hxy.2.2.2.1, hxy.2.2.2.2.2⟩) y'
      (mem_filter.mpr ⟨(Mole.mem_dartsAt M v y').mpr hxy'.2.1, hxy'.2.2.2.1, hxy'.2.2.2.2.2⟩)

theorem source_nested_joint_pairs_compatible {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] (M : Molecule V D) {A S : Finset V} {a b v : V}
    (hAS : A ⊆ S) (hS : M.IsBlock S a b) (hv : v = a ∨ v = b) {x y x' y' : D}
    (hxy : SourceJointPair M A v x y) (hxy' : SourceJointPair M S v x' y') : x = x' ∧ y = y' := by
  apply source_joint_pair_unique M hS hv _ hxy'
  exact ⟨hxy.1, hxy.2.1, ⟨hAS hxy.2.2.1.1, hAS hxy.2.2.1.2⟩,
    ⟨hAS hxy.2.2.2.1.1, hAS hxy.2.2.2.1.2⟩, hxy.2.2.2.2⟩

/-- An un-oriented source pair agrees with the unique oriented pair up to reversal. -/
theorem source_joint_pair_eq_or_swap {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] (M : Molecule V D) {S : Finset V} {a b v : V}
    (hB : M.IsBlock S a b) (hv : v = a ∨ v = b) {x y x₀ y₀ : D}
    (hxy₀ : SourceJointPair M S v x₀ y₀)
    (hx : M.atom x = v) (hy : M.atom y = v) (hgx : M.InGroup S x) (hgy : M.InGroup S y)
    (ho : M.out x ≠ M.out y) :
    (x = x₀ ∧ y = y₀) ∨ (x = y₀ ∧ y = x₀) := by
  by_cases hox : M.out x = true
  · have hoy : M.out y = false := by cases hy' : M.out y <;> simp_all
    exact Or.inl (source_joint_pair_unique M hB hv ⟨hx, hy, hgx, hgy, hox, hoy⟩ hxy₀)
  · have hox' : M.out x = false := by cases hx' : M.out x <;> simp_all
    have hoy : M.out y = true := by cases hy' : M.out y <;> simp_all
    have hh := source_joint_pair_unique M hB hv ⟨hy, hx, hgy, hgx, hoy, hox'⟩ hxy₀
    exact Or.inr ⟨hh.2, hh.1⟩

end WaveTurbulence.LGSpine
