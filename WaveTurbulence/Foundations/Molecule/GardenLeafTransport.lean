/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.GardenMoleculeDefs
import Mathlib.Tactic

/-! # Transporting a garden pairing to a concrete new forest
The helper is conditional on structural leaf-transport data. Its CL
application derives those data from the actual boundary construction.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} (G : Garden w) (P : GLeaf G.tree → Prop)

/-- Restrict the actual pairing to a pairing-closed leaf family. -/
@[expose] def restrictedLeafPair (hc : ∀ l, P l → P (G.pair l)) (l : {l // P l}) : {l // P l} :=
  ⟨G.pair l.1,hc l.1 l.2⟩

theorem restrictedLeafPair_involutive (hc : ∀ l, P l → P (G.pair l)) :
    Function.Involutive (restrictedLeafPair G P hc) := fun l => Subtype.ext (G.pair_pair l.1)

variable {newTree : Fin w → TTree}

/-- Conjugate the literal old pairing by the supplied leaf bijection. -/
@[expose] def transportedLeafPair (hc : ∀ l, P l → P (G.pair l))
    (e : GLeaf newTree ≃ {l // P l}) (l : GLeaf newTree) : GLeaf newTree :=
  e.symm (restrictedLeafPair G P hc (e l))

theorem transportedLeafPair_comm (hc : ∀ l, P l → P (G.pair l))
    (e : GLeaf newTree ≃ {l // P l}) (l : GLeaf newTree) :
    e (transportedLeafPair G P hc e l) = restrictedLeafPair G P hc (e l) :=
  e.apply_symm_apply _

theorem transportedLeafPair_involutive (hc : ∀ l, P l → P (G.pair l))
    (e : GLeaf newTree ≃ {l // P l}) : Function.Involutive (transportedLeafPair G P hc e) := by
  intro l
  apply e.injective
  rw [transportedLeafPair_comm,transportedLeafPair_comm,restrictedLeafPair_involutive]

theorem transportedLeafPair_eq_iff (hc : ∀ l, P l → P (G.pair l))
    (e : GLeaf newTree ≃ {l // P l}) (l : GLeaf newTree) :
    transportedLeafPair G P hc e l = l ↔ G.pair (e l).1 = (e l).1 := by
  constructor
  · intro h
    have hcomm := congrArg Subtype.val (transportedLeafPair_comm G P hc e l)
    rw [h] at hcomm
    exact hcomm.symm
  · intro h
    apply e.injective
    rw [transportedLeafPair_comm]
    exact Subtype.ext h

/-- A concrete new garden, using the old marks and the old pairing on
retained leaves. The hypotheses are signed rooted-forest transport data. -/
@[expose] def gardenOfLeafTransport (hc : ∀ l, P l → P (G.pair l))
    (e : GLeaf newTree ≃ {l // P l})
    (hs : ∀ l : GLeaf newTree, nodeSign G.sig l.1 = nodeSign G.sig (e l).1.1) : Garden w where
  sig := G.sig
  tree := newTree
  pair := transportedLeafPair G P hc e
  mark l := G.mark (e l).1
  pair_pair := transportedLeafPair_involutive G P hc e
  pair_eq_iff l := (transportedLeafPair_eq_iff G P hc e l).trans (G.pair_eq_iff (e l).1)
  pair_sign l hn := by
    have hne : G.pair (e l).1 ≠ (e l).1 := fun h => hn ((transportedLeafPair_eq_iff G P hc e l).mpr h)
    have hcomm := congrArg Subtype.val (transportedLeafPair_comm G P hc e l)
    rw [hs,hs,hcomm]
    exact G.pair_sign (e l).1 hne

end WaveTurbulence.Mole
