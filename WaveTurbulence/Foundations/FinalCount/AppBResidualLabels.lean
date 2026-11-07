/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTwoBoundaryConnectivity
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # Figure labels and actual residual components -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

theorem vertex_eq_iff (a b : ℕ) (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) :
    r.vertex a = r.vertex b ↔ a = b :=
  ⟨fun h => r.vertex_injective ha hb h,fun h => congrArg r.vertex h⟩

theorem residual_vertex_mem_iff (a b : ℕ) (hb : b ∈ P.vertices) (hkb : b ∉ P.removed) :
    r.vertex b ∈ Degen.residualComponent M r.removedAtoms (r.vertex a) ↔
      r.post.SameComponent (r.vertex a) (r.vertex b) := by
  classical
  rw [Degen.mem_residualComponent]
  constructor
  · intro h
    exact (Degen.eraseAtoms_sameComponent_iff M r.removedAtoms _ _).mpr h.2.2
  · intro h
    refine ⟨r.vertex_mem b hb,?_,(Degen.eraseAtoms_sameComponent_iff M r.removedAtoms _ _).mp h⟩
    exact fun hy => hkb ((r.vertex_mem_removed_iff b hb).mp hy)

theorem removed_vertex_not_in_residual (a b : ℕ) (hb : b ∈ P.removed) :
    r.vertex b ∉ Degen.residualComponent M r.removedAtoms (r.vertex a) := by
  intro h
  exact ((Degen.mem_residualComponent M r.removedAtoms (r.vertex a) _).mp h).2.1 (mem_image_of_mem _ hb)

/-- A representative connected to every surviving displayed label connects
the whole actual post graph. -/
theorem post_connected_of_boundary_representative (a : ℕ)
    (hconn : ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v)
    (hne : P.removed.Nonempty)
    (hlabels : ∀ b ∈ P.vertices, b ∉ P.removed → r.post.SameComponent (r.vertex a) (r.vertex b)) :
    ∀ v ∈ r.post.atoms, ∀ w ∈ r.post.atoms, r.post.SameComponent v w := by
  apply r.post_connected_of_displayed hconn hne
  intro x hx hkx y hy hky
  exact Relation.EqvGen.trans _ _ _ (hlabels x hx hkx).symm (hlabels y hy hky)

end AppbRealization
end WaveTurbulence.Mole
