/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.OpEPiece
import Mathlib.Tactic

/-! # The theta chain from data on the ambient molecule (packet L6-COUNT, item D)

`opE_one`, `opE_two` take the shape `IsThetaChain` of the piece `𝕄[S]` (whose darts are `RetainedDart`s). This module
derives it from facts about the ambient molecule `N` (`ThetaData`): the darts of `N` at `p` (resp. `q`) whose far end
lies in `S` are exactly `a, b, z₁` (resp. `mate a, mate b, z₂`); the chain `C = S ∖ {p, q}` has no exit, in = out = 1
and is connected in `𝕄[C]`; no three equal signs at `p`; `out z₁ ≠ out z₂`.

* `ThetaData`, `ThetaData.isThetaChain`: the shape on the piece, with the darts `pieceDart N S z _` (whose `val` is `z`,
  so the gap hypothesis of `opE_one`/`opE_two` reads `‖k_{z₁} − k_{z₂}‖ ≥ ρ` with the darts of `N`).
* `piece_outdeg_eq`, `piece_indeg_eq`: degrees at an atom of `S` all of whose bonds stay in `S`.
* `sameComponent_piece_piece`: connectivity of `𝕄[C]` passes to `(𝕄[S])[C]`. -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.Count
open WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The theta chain, described in the ambient molecule `N`.** -/
structure ThetaData (N : Molecule V D) (S : Finset V) (p q : V) (a b z₁ z₂ : D) : Prop where
  sub : S ⊆ N.atoms
  hp : p ∈ S
  hq : q ∈ S
  hpq : p ≠ q
  ha : N.atom a = p
  hb : N.atom b = p
  hz₁ : N.atom z₁ = p
  hz₂ : N.atom z₂ = q
  hma : N.atom (N.mate a) = q
  hmb : N.atom (N.mate b) = q
  hab : a ≠ b
  hmz₁ : N.atom (N.mate z₁) ∈ S \ {p, q}
  hmz₂ : N.atom (N.mate z₂) ∈ S \ {p, q}
  pin : ∀ z, N.atom z = p → N.atom (N.mate z) ∈ S → z = a ∨ z = b ∨ z = z₁
  qin : ∀ z, N.atom z = q → N.atom (N.mate z) ∈ S → z = N.mate a ∨ z = N.mate b ∨ z = z₂
  signs : ¬ (N.out a = N.out b ∧ N.out b = N.out z₁)
  dir : N.out z₁ ≠ N.out z₂
  closed : ∀ z, N.atom z ∈ S \ {p, q} → N.atom (N.mate z) ∈ S
  chain : ∀ v ∈ S \ {p, q}, N.outdeg v = 1 ∧ N.indeg v = 1
  conn : ∀ u ∈ S \ {p, q}, ∀ v ∈ S \ {p, q}, (piece N (S \ {p, q})).SameComponent u v

/-- Degrees at an atom of `S` whose bonds all stay in `S` are those of `N`. -/
theorem piece_deg_filter_eq {N : Molecule V D} {S : Finset V} {v : V}
    (hcl : ∀ z, N.atom z = v → N.atom (N.mate z) ∈ S) (hv : v ∈ S) (f : Bool → Prop) [DecidablePred f] :
    (((piece N S).dartsAt v).filter fun x => f ((piece N S).out x)).card =
      ((N.dartsAt v).filter fun x => f (N.out x)).card := by
  classical
  refine card_bij (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and] at hx ⊢
    exact hx
  · intro x _ y _ h; exact Subtype.ext h
  · intro z hz
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and] at hz
    have hz1 : N.atom z ∈ S := hz.1 ▸ hv
    refine ⟨pieceDart N S z ⟨hz1, hcl z hz.1⟩, ?_, rfl⟩
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and]
    exact hz

theorem piece_outdeg_eq {N : Molecule V D} {S : Finset V} {v : V}
    (hcl : ∀ z, N.atom z = v → N.atom (N.mate z) ∈ S) (hv : v ∈ S) : (piece N S).outdeg v = N.outdeg v :=
  piece_deg_filter_eq hcl hv (fun b => b = true)

theorem piece_indeg_eq {N : Molecule V D} {S : Finset V} {v : V}
    (hcl : ∀ z, N.atom z = v → N.atom (N.mate z) ∈ S) (hv : v ∈ S) : (piece N S).indeg v = N.indeg v :=
  piece_deg_filter_eq hcl hv (fun b => b = false)

/-- Connectivity of `𝕄[C]` passes to the piece of the piece `(𝕄[S])[C]`, `C ⊆ S`. -/
theorem sameComponent_piece_piece {N : Molecule V D} {S C : Finset V} (hCS : C ⊆ S) {u v : V}
    (h : (piece N C).SameComponent u v) : (piece (piece N S) C).SameComponent u v := by
  induction h with
  | rel a b hab =>
    obtain ⟨z, rfl, rfl⟩ := hab
    have hm := piece_dart_mem z
    have h1 : N.atom z.val ∈ S ∧ N.atom (N.mate z.val) ∈ S := ⟨hCS hm.1, hCS hm.2⟩
    let z₁ : Degen.RetainedDart N (N.atoms \ S) := pieceDart N S z.val h1
    have h2 : (piece N S).atom z₁ ∈ C ∧ (piece N S).atom ((piece N S).mate z₁) ∈ C := hm
    exact Relation.EqvGen.rel _ _ ⟨pieceDart (piece N S) C z₁ h2, rfl, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

namespace ThetaData
variable {N : Molecule V D} {S : Finset V} {p q : V} {a b z₁ z₂ : D} (h : ThetaData N S p q a b z₁ z₂)
include h

end ThetaData
end

end WaveTurbulence.GammaLow.FinalCount.Count
