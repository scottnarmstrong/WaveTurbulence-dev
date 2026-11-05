/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineGroupGaps
import Mathlib.Tactic

/-! # Flow sums in the actual induced half-edge carrier -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D]
    [AddCommGroup E] [Module ℝ E]

/-- The full local flow in the induced carrier is exactly the group's
restricted flow in the ambient molecule. -/
theorem induced_localFlow (M : Molecule V D) (S : Finset V) (k : D → E) (v : V) :
    (∑ x ∈ (Mole.induced M S).dartsAt v,
      (Mole.induced M S).dartSign x • k x.1)=groupFlow M S k v := by
  unfold groupFlow
  apply Finset.sum_bij (fun x _ => x.1)
  · intro x hx
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v x.1).mpr
      ((Mole.mem_dartsAt (Mole.induced M S) v x).mp hx),x.2⟩
  · intro x _hx y _hy he
    exact Subtype.ext he
  · intro y hy
    obtain ⟨ha,hg⟩ := mem_filter.mp hy
    exact ⟨⟨y,hg⟩,(Mole.mem_dartsAt (Mole.induced M S) v _).mpr
      ((Mole.mem_dartsAt M v y).mp ha),rfl⟩
  · intro x _hx
    rfl

end WaveTurbulence.Vine
