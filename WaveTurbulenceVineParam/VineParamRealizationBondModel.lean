/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedBondChart
public import WaveTurbulenceVineParam.VineParamRealizedModel
public import WaveTurbulenceVineParam.VineParamContractBridge
import Mathlib.Tactic

/-! # Actual complete bond model of every expanded source vine -/

public section
namespace WaveTurbulence.Vine.Param
open Finset VineParamContract
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The finite template range and the actual atom group are equivalent,
with the exact source realization as the inverse. -/
@[expose] noncomputable def realizationAtomEquiv {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b) :
    Fin (X.expand R.k).n ≃ ↥S where
  toFun := R.atomAt
  invFun v := ⟨R.f v,mem_range.mp (R.image_eq ▸ mem_image.mpr ⟨v,v.2,rfl⟩)⟩
  left_inv i := Fin.ext (R.label_atomAt i)
  right_inv v := by
    apply Subtype.ext
    apply R.injOn (R.atomAt _).2 v.2
    exact R.label_atomAt _

/-- Lift literal directed endpoint labels to their exact bounded source
atom carrier. Every actual internal bond occurs exactly once. -/
@[expose] noncomputable def realizationBondModel {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (e : Fin (X.expand R.k).bonds.length ≃ internalBonds M S) :
    DirectedBondModel M S (Fin (X.expand R.k).n) (Fin (X.expand R.k).bonds.length) where
  ends j := (⟨(realizedEnds R e j).1,(realizedEnds_bounds R e j).1⟩,
    ⟨(realizedEnds R e j).2,(realizedEnds_bounds R e j).2⟩)
  atom := realizationAtomEquiv R
  edge := contractEnumeration M S e
  tail := by
    intro j
    change M.atom (e j).1=(R.atomAt _).1
    apply (label_eq_iff_atomAt R (mem_filter.mp (e j).2).2.2.1 _).mp
    rfl
  head := by
    intro j
    change M.atom (M.mate (e j).1)=(R.atomAt _).1
    apply (label_eq_iff_atomAt R (mem_filter.mp (e j).2).2.2.2 _).mp
    rfl

end WaveTurbulence.Vine.Param
