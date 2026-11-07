/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.Closed
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapGarden
/-! FLOWER-P7: the combinatorics of the component of the first tree of the decapitated garden.
The six child trees have the alternating signs `(+,-,+,-,+,-)`; a closed set of trees containing tree `0`
is balanced, hence one of ten explicit sets. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

theorem childSig_val (c : Fin (2 * 3)) : ((childSig c : ℤˣ) : ℤ) = if c.val % 2 = 0 then 1 else -1 := by
  fin_cases c <;> decide

/-- The ten admissible components of the first tree. -/
def shapeList : List (Finset (Fin (2 * 3))) :=
  [{0, 1}, {0, 3}, {0, 5}, {0, 3, 4, 5}, {0, 1, 4, 5}, {0, 1, 3, 4}, {0, 2, 3, 5}, {0, 1, 2, 5}, {0, 1, 2, 3},
    Finset.univ]

theorem shape_classify : ∀ S : Finset (Fin (2 * 3)), 0 ∈ S →
    (∑ j ∈ S, (if j.val % 2 = 0 then (1 : ℤ) else -1)) = 0 → S ∈ shapeList := by
  decide

/-- A shape table: the first block (containing tree `0` at index `0`) and the second block, as an
equivalence `Fin a ⊕ Fin b ≃ Fin 6`. -/
noncomputable def tableEquiv {a b : ℕ} (f : Fin a → Fin (2 * 3)) (g : Fin b → Fin (2 * 3))
    (h : Function.Bijective (Sum.elim f g)) : Fin a ⊕ Fin b ≃ Fin (2 * 3) :=
  Equiv.ofBijective _ h

/-- Component `{0,1}`, rest `(2,3,4,5)`. -/
noncomputable def σ1 : Fin 2 ⊕ Fin 4 ≃ Fin (2 * 3) :=
  tableEquiv ![0, 1] ![2, 3, 4, 5] (by decide)
/-- Component `{0,3}`, rest `(2,1,4,5)`. -/
noncomputable def σ2 : Fin 2 ⊕ Fin 4 ≃ Fin (2 * 3) :=
  tableEquiv ![0, 3] ![2, 1, 4, 5] (by decide)
/-- Component `{0,5}`, rest `(2,1,4,3)`. -/
noncomputable def σ3 : Fin 2 ⊕ Fin 4 ≃ Fin (2 * 3) :=
  tableEquiv ![0, 5] ![2, 1, 4, 3] (by decide)
/-- Component `{0,3,4,5}`, rest `(2,1)`. -/
noncomputable def σ4 : Fin 4 ⊕ Fin 2 ≃ Fin (2 * 3) :=
  tableEquiv ![0, 3, 4, 5] ![2, 1] (by decide)
/-- Component `{0,1,4,5}`, rest `(2,3)`. -/
noncomputable def σ5 : Fin 4 ⊕ Fin 2 ≃ Fin (2 * 3) :=
  tableEquiv ![0, 1, 4, 5] ![2, 3] (by decide)
/-- Component `{0,1,3,4}`, rest `(2,5)`. -/
noncomputable def σ6 : Fin 4 ⊕ Fin 2 ≃ Fin (2 * 3) :=
  tableEquiv ![0, 1, 3, 4] ![2, 5] (by decide)
/-- Component `{0,2,3,5}`, rest `(4,1)`. -/
noncomputable def σ7 : Fin 4 ⊕ Fin 2 ≃ Fin (2 * 3) :=
  tableEquiv ![0, 2, 3, 5] ![4, 1] (by decide)
/-- Component `{0,1,2,5}`, rest `(4,3)`. -/
noncomputable def σ8 : Fin 4 ⊕ Fin 2 ≃ Fin (2 * 3) :=
  tableEquiv ![0, 1, 2, 5] ![4, 3] (by decide)
/-- Component `{0,1,2,3}`, rest `(4,5)`. -/
noncomputable def σ9 : Fin 4 ⊕ Fin 2 ≃ Fin (2 * 3) :=
  tableEquiv ![0, 1, 2, 3] ![4, 5] (by decide)

/-- Second-level split of a width-four block ordered `(+,-,+,-)`: `(0,1)(2,3)`. -/
noncomputable def τ1 : Fin 2 ⊕ Fin 2 ≃ Fin 4 := Equiv.ofBijective (Sum.elim ![0, 1] ![2, 3]) (by decide)
/-- Second-level split of a width-four block ordered `(+,-,+,-)`: `(0,3)(2,1)`. -/
noncomputable def τ2 : Fin 2 ⊕ Fin 2 ≃ Fin 4 := Equiv.ofBijective (Sum.elim ![0, 3] ![2, 1]) (by decide)

/-- Every plain garden with the alternating signature has a minimal closed block of tree `0` among the ten shapes. -/
theorem exists_shape (G : Garden (2 * 3)) (hplain : G.IsPlain) (hsig : ∀ c, G.sig c = childSig c) :
    ∃ S ∈ shapeList, MinimalAt G 0 S := by
  obtain ⟨S, hS⟩ := exists_minimal_closed G hplain 0
  refine ⟨S, shape_classify S hS.1 ?_, hS⟩
  have := balanced_of_closed G S hS.2.1
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => by rw [hsig j, childSig_val]

end WaveTurbulence.FlowerP7
