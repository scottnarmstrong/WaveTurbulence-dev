/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineGroupGaps
import Mathlib.Tactic

/-! # A block's signed joint flow is always an actual gap -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D E : Type*} [DecidableEq V] [Fintype D] [AddCommGroup E] [Module ℝ E]

/-- The source block axioms supply one actual outgoing and incoming dart
at each joint. Their difference equals the complete signed joint flow. -/
theorem block_groupGap_exists (M : Molecule V D) {S : Finset V} {a b : V}
    (hB : M.IsBlock S a b) (k : D → E) : IsGroupGap M S k a (groupFlow M S k a) := by
  classical
  have ho := hB.2.2.2.2.1
  have hi := hB.2.2.2.2.2.1
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<((M.dartsAt a).filter
    (fun x => M.InGroup S x ∧ M.out x=true)).card from by change 0<M.outIn S a; omega)
  obtain ⟨y,hy⟩ := card_pos.mp (show 0<((M.dartsAt a).filter
    (fun x => M.InGroup S x ∧ M.out x=false)).card from by change 0<M.inIn S a; omega)
  obtain ⟨hxa,hxg,hxo⟩ := mem_filter.mp hx
  obtain ⟨hya,hyg,hyo⟩ := mem_filter.mp hy
  have hg : IsGroupGap M S k a (k x-k y) :=
    ⟨x,y,(Mole.mem_dartsAt M a x).mp hxa,(Mole.mem_dartsAt M a y).mp hya,hxg,hyg,hxo,hyo,rfl⟩
  exact (groupGap_eq_flow M (Mole.block_joint_degrees M hB).1 hg) ▸ hg

end WaveTurbulence.Vine
