/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBResidualLabels
import Mathlib.Tactic

/-! # The allowed interchange of the two right-hand boundary labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} (r : AppbRealization M AppbPatternKind.s33.pattern)

theorem appb_s33_swap_vertex_mem (a : ℕ) (ha : a ∈ AppbPatternKind.s33.pattern.vertices) :
    Equiv.swap 5 6 a ∈ AppbPatternKind.s33.pattern.vertices := by
  have hh : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by
    have hV : AppbPatternKind.s33.pattern.vertices = {1,2,3,4,5,6} := by decide
    simpa only [hV,mem_insert,mem_singleton] using ha
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

noncomputable def s33SwapBoundary : AppbRealization M AppbPatternKind.s33.pattern := by
  classical
  let σ : Equiv.Perm ℕ := Equiv.swap 5 6
  let v' := fun j => r.vertex (σ j)
  have hY : AppbPatternKind.s33.pattern.removed.image v' = r.removedAtoms := by
    change ({1,2} : Finset ℕ).image v' = ({1,2} : Finset ℕ).image r.vertex
    simp only [image_insert,image_singleton]
    rfl
  let τ : Equiv.Perm (Fin 5) := Equiv.swap 3 4
  let e : Fin 5 ≃ {x // x ∈ appbRemovedBonds M (AppbPatternKind.s33.pattern.removed.image v')} :=
    τ.trans (r.edge.trans (Equiv.subtypeEquivRight (fun x => by rw [hY]; rfl)))
  exact {
    vertex := v'
    vertex_injective := by
      intro a ha b hb he
      exact σ.injective (r.vertex_injective (AppbRealization.appb_s33_swap_vertex_mem a ha) (AppbRealization.appb_s33_swap_vertex_mem b hb) he)
    vertex_mem := fun a ha => r.vertex_mem _ (AppbRealization.appb_s33_swap_vertex_mem a ha)
    edge := e
    endpoints := by
      intro i
      change M.ends (r.edge (τ i)).val =
        s(r.vertex (σ (AppbPatternKind.s33.pattern.edges[i].1)),r.vertex (σ (AppbPatternKind.s33.pattern.edges[i].2)))
      have he := r.endpoints (τ i)
      rw [he]
      fin_cases i <;> rfl
  }

theorem s33SwapBoundary_vertex (a : ℕ) : r.s33SwapBoundary.vertex a = r.vertex (Equiv.swap 5 6 a) := rfl

theorem s33SwapBoundary_removed : r.s33SwapBoundary.removedAtoms = r.removedAtoms := by
  change ({1,2} : Finset ℕ).image (fun j => r.vertex (Equiv.swap 5 6 j)) = ({1,2} : Finset ℕ).image r.vertex
  simp only [image_insert,image_singleton]
  rfl

theorem s33SwapBoundary_sameComponent (a b : V) :
    r.s33SwapBoundary.post.SameComponent a b ↔ r.post.SameComponent a b := by
  change (Degen.eraseAtoms M r.s33SwapBoundary.removedAtoms).SameComponent a b ↔
    (Degen.eraseAtoms M r.removedAtoms).SameComponent a b
  rw [r.s33SwapBoundary_removed]

theorem s33SwapBoundary_components : r.s33SwapBoundary.post.numComponents = r.post.numComponents := by
  change (Degen.eraseAtoms M r.s33SwapBoundary.removedAtoms).numComponents =
    (Degen.eraseAtoms M r.removedAtoms).numComponents
  rw [r.s33SwapBoundary_removed]

end AppbRealization
end WaveTurbulence.Mole
