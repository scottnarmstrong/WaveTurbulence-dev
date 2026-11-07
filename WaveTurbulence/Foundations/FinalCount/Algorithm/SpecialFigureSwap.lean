/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBRealizations
import Mathlib.Tactic

/-! # Exchanging the two centers and double tails of the actual special figure -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def swapSpecialFigure {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33new3.pattern) :
    AppbRealization M AppbPatternKind.s33new3.pattern := by
  classical
  let σ : Equiv.Perm ℕ := (Equiv.swap 1 2).trans (Equiv.swap 3 4)
  let τ : Equiv.Perm (Fin 5) := Equiv.ofBijective ![0,3,4,1,2] (by decide)
  let f := r.vertex ∘ σ
  have hσ : ∀ a ∈ AppbPatternKind.s33new3.pattern.vertices,σ a ∈ AppbPatternKind.s33new3.pattern.vertices := by
    dsimp only [σ]
    decide
  have hY : AppbPatternKind.s33new3.pattern.removed.image f = r.removedAtoms := by
    change ({1,2} : Finset ℕ).image f = ({1,2} : Finset ℕ).image r.vertex
    simp only [image_insert,image_singleton]
    change {r.vertex 2,r.vertex 1} = {r.vertex 1,r.vertex 2}
    exact pair_comm _ _
  exact {
    vertex := f
    vertex_injective := by
      intro a ha b hb he
      exact σ.injective (r.vertex_injective (hσ a ha) (hσ b hb) he)
    vertex_mem := fun a ha => r.vertex_mem _ (hσ a ha)
    edge := (τ.trans r.edge).trans (Equiv.subtypeEquivRight (fun x => by rw [hY]; rfl))
    endpoints := by
      intro i
      fin_cases i
      · change M.ends (r.edge (0 : Fin 5)).val = s(r.vertex 2,r.vertex 1)
        exact (r.endpoints (0 : Fin 5)).trans Sym2.eq_swap
      · exact r.endpoints (3 : Fin 5)
      · exact r.endpoints (4 : Fin 5)
      · exact r.endpoints (1 : Fin 5)
      · exact r.endpoints (2 : Fin 5)
  }

theorem swapSpecialFigure_vertex_one {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33new3.pattern) : (swapSpecialFigure r).vertex 1 = r.vertex 2 := rfl

theorem swapSpecialFigure_vertex_two {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.s33new3.pattern) : (swapSpecialFigure r).vertex 2 = r.vertex 1 := rfl

end WaveTurbulence.Mole.AppbAlgorithm
