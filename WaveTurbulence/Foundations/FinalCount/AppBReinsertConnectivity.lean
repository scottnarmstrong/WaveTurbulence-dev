/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponents
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # Residual component representatives remain reachable after reinsertion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appb_induced_sameComponent_ambient (M : Molecule V D) (S : Finset V)
    {a b : V} (h : (induced M S).SameComponent a b) : M.SameComponent a b := by
  induction h with
  | rel u v h => exact Relation.EqvGen.rel _ _ ((induced_adj_iff M S u v).mp h).1
  | refl u => exact Relation.EqvGen.refl u
  | symm u v h ih => exact ih.symm
  | trans u v w h h' ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

theorem appb_twoComponents_reaches (M : Molecule V D) {a b : V}
    (h : TwoComponents M M.atoms a b) {v : V} (hv : v ∈ M.atoms) :
    M.SameComponent v a ∨ M.SameComponent v b := by
  obtain ⟨U,W,hcover,hdis,hU,hW,ha,hb,hno⟩ := h
  rcases mem_union.mp (hcover.symm ▸ hv) with hv | hv
  · exact Or.inl (appb_induced_sameComponent_ambient M U (hU.2 v hv a ha))
  · exact Or.inr (appb_induced_sameComponent_ambient M W (hW.2 v hv b hb))

theorem appb_sameComponent_addBond (M : Molecule V D) (a b : V) {u v : V}
    (h : M.SameComponent u v) : (addBond M a b).SameComponent u v := by
  induction h with
  | rel u v h =>
    obtain ⟨x,hx,hy⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨Sum.inl x,hx,hy⟩
  | refl u => exact Relation.EqvGen.refl u
  | symm u v h ih => exact ih.symm
  | trans u v w h h' ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem sameComponent_directedPostWithBond (a b : ℕ) (i : Fin P.edges.length)
    {u v : V} (h : r.post.SameComponent u v) :
    (r.directedPostWithBond a b i).SameComponent u v := by
  unfold directedPostWithBond
  split_ifs <;> exact appb_sameComponent_addBond _ _ _ h

end AppbRealization
end WaveTurbulence.Mole
