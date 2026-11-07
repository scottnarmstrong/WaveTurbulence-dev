/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrame
import Mathlib.Tactic

/-! # Reindexing an actual triple support without a counting loss -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbTripleFrame
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (t : AppbTripleFrame r v)

def reindex (π : Equiv.Perm (Fin 3)) : AppbTripleFrame r v where
  index := π.toEmbedding.trans t.index
  incidence := fun j => t.incidence (π j)
  other := by
    intro i hi
    apply t.other i
    intro j hj
    apply hi (π.symm j)
    simpa using hj

theorem reindex_project_card {K : Type*} [DecidableEq K]
    (π : Equiv.Perm (Fin 3)) (Q : Finset (Fin P.edges.length → K)) :
    (Q.image (t.reindex π).project).card = (Q.image t.project).card := by
  classical
  let f : (Fin 3 → K) → (Fin 3 → K) := fun q j => q (π j)
  have hf : Function.Injective f := by
    intro q q' he
    funext j
    have hh := congrFun he (π.symm j)
    simpa only [f,π.apply_symm_apply] using hh
  have he : Q.image (t.reindex π).project = (Q.image t.project).image f := by
    rw [image_image]
    rfl
  rw [he,card_image_of_injective _ hf]

end AppbTripleFrame
end WaveTurbulence.Mole
