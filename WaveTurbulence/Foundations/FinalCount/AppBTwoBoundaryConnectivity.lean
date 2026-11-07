/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBPostConnectivity
import Mathlib.Tactic

/-! # Residual connectivity from two surviving figure labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- A finite incidence-table reduction of full residual connectivity. -/
theorem post_connected_of_two_boundary_labels (a b : ℕ)
    (hlabels : P.vertices \ P.removed = {a,b}) (hne : P.removed.Nonempty)
    (hab : r.post.SameComponent (r.vertex a) (r.vertex b))
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) :
    ∀ v ∈ r.post.atoms, ∀ w ∈ r.post.atoms, r.post.SameComponent v w := by
  apply r.post_connected_of_displayed hconn hne
  intro x hx hkx y hy hky
  have hx' : x = a ∨ x = b := by
    have hh : x ∈ P.vertices \ P.removed := mem_sdiff.mpr ⟨hx,hkx⟩
    rw [hlabels] at hh
    simpa only [mem_insert,mem_singleton] using hh
  have hy' : y = a ∨ y = b := by
    have hh : y ∈ P.vertices \ P.removed := mem_sdiff.mpr ⟨hy,hky⟩
    rw [hlabels] at hh
    simpa only [mem_insert,mem_singleton] using hh
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact Relation.EqvGen.refl _
  · exact hab
  · exact hab.symm
  · exact Relation.EqvGen.refl _

end AppbRealization
end WaveTurbulence.Mole
