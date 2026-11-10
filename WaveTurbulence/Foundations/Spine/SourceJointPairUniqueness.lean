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

end WaveTurbulence.LGSpine
