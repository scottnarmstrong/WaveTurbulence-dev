/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.D33Continuation
public import WaveTurbulence.Foundations.FinalCount.Algorithm.S33SwapComponents
import Mathlib.Tactic

/-! # Literal orientation of the next displayed double-rung head -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset

def d33HeadPermutation : Equiv.Perm ℕ := (Equiv.swap 1 2).trans (Equiv.swap 3 4)

theorem d33HeadPermutation_mem : ∀ a ∈ AppbPatternKind.d33.pattern.vertices,
    d33HeadPermutation a ∈ AppbPatternKind.d33.pattern.vertices := by decide

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def swapD33Heads {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) : AppbRealization M AppbPatternKind.d33.pattern := by
  let σ := d33HeadPermutation
  let v' := fun a => r.vertex (σ a)
  have hY : AppbPatternKind.d33.pattern.removed.image v' = r.removedAtoms := by
    change ({1,2} : Finset ℕ).image v' = ({1,2} : Finset ℕ).image r.vertex
    simp only [image_insert,image_singleton]
    change ({r.vertex 2,r.vertex 1} : Finset V) = {r.vertex 1,r.vertex 2}
    exact pair_comm _ _
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
  let e : Fin 4 ≃ {x // x ∈ appbRemovedBonds M (AppbPatternKind.d33.pattern.removed.image v')} :=
    τ.trans (r.edge.trans (Equiv.subtypeEquivRight (fun x => by rw [hY]; rfl)))
  exact {
    vertex := v'
    vertex_injective := by
      intro a ha b hb he
      exact σ.injective (r.vertex_injective (d33HeadPermutation_mem a ha) (d33HeadPermutation_mem b hb) he)
    vertex_mem := fun a ha => r.vertex_mem _ (d33HeadPermutation_mem a ha)
    edge := e
    endpoints := by
      intro i
      change M.ends (r.edge (τ i)).val =
        s(r.vertex (σ AppbPatternKind.d33.pattern.edges[i].1),r.vertex (σ AppbPatternKind.d33.pattern.edges[i].2))
      have he := r.endpoints (τ i)
      rw [he]
      fin_cases i <;> first | rfl | exact Sym2.eq_swap }

theorem swapD33Heads_opposite {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33.pattern) (h : AppbD33BoundaryOpposite M r) :
    AppbD33BoundaryOpposite M (swapD33Heads r) := by
  change AppbOppositeFrom M (r.vertex 2) (r.vertex 1) (r.edge (3 : Fin 4)).val (r.edge (2 : Fin 4)).val
  exact (oppositeFrom_swap_iff M _ _ _ _).mp h

/-- The source's next rung can be oriented literally, including when an
existential witness originally enumerated its two centers in reverse. -/
theorem D33Continues.oriented {M : Molecule V D}
    {r : AppbRealization M AppbPatternKind.d33.pattern} (h : D33Continues r) :
    ∃ t : AppbRealization r.post AppbPatternKind.d33.pattern,
      t.vertex 1 = r.vertex 3 ∧ t.vertex 2 = r.vertex 4 ∧ AppbD33BoundaryOpposite r.post t := by
  obtain ⟨t,ht,ho⟩ := h
  rcases ht with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact ⟨t,h1,h2,ho⟩
  · refine ⟨swapD33Heads t,?_,?_,swapD33Heads_opposite t ho⟩
    · change t.vertex 2 = r.vertex 3
      exact h2
    · change t.vertex 1 = r.vertex 4
      exact h1

end WaveTurbulence.Mole.AppbAlgorithm
