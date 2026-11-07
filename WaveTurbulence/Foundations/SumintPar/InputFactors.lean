/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.InputGrouping

/-!
# Heterogeneous independent factor inputs

The three kinds of source factor carry one, two and three lattice
variables. Their dependent function space is exactly equivalent to the
original full lattice input, with the source slots preserved literally.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- Linear, pair and normal factor indices. -/
abbrev FactorIdx (S : SumintShape) := Fin S.I ⊕ (Σ i : Fin S.I, Fin (S.m i)) ⊕
  {i : Fin S.I // S.nor i = true}

/-- The actual variable type of each source factor. -/
@[expose] def FactorInput (S : SumintShape) (α : Type*) : FactorIdx S → Type _
  | .inl _ => α
  | .inr (.inl _) => α × α
  | .inr (.inr _) => Fin 3 → α

/-- Reassemble the grouped tuple as a dependent family of independent factor inputs. -/
@[expose] def factorGroupingEquiv (S : SumintShape) (α : Type*) :
    ((Fin S.I → α) × ((Σ i : Fin S.I, Fin (S.m i)) → α × α) ×
      ({i : Fin S.I // S.nor i = true} → Fin 3 → α)) ≃
      ((a : FactorIdx S) → FactorInput S α a) where
  toFun z
    | .inl i => z.1 i
    | .inr (.inl p) => z.2.1 p
    | .inr (.inr i) => z.2.2 i
  invFun z := (fun i => z (.inl i),fun p => z (.inr (.inl p)),fun i => z (.inr (.inr i)))
  left_inv z := by rcases z with ⟨a,b,c⟩; rfl
  right_inv z := by
    funext a
    rcases a with i | (p | i) <;> rfl

/-- The full source lattice is exactly the product of the independent factor lattices. -/
@[expose] noncomputable def inputFactorEquiv (S : SumintShape) (α : Type*) :
    (S.VIdx → α) ≃ ((a : FactorIdx S) → FactorInput S α a) :=
  (inputGroupingEquiv S α).trans (factorGroupingEquiv S α)

/-- Linear factor evaluation uses exactly x0. -/
theorem inputFactorEquiv_linear (S : SumintShape) {α : Type*} (x : S.VIdx → α) (i : Fin S.I) :
    inputFactorEquiv S α x (.inl i) = x (S.x0Slot i) := rfl

/-- Pair factor evaluation uses exactly the x/y pair. -/
theorem inputFactorEquiv_pair (S : SumintShape) {α : Type*} (x : S.VIdx → α)
    (p : Σ i : Fin S.I, Fin (S.m i)) :
    inputFactorEquiv S α x (.inr (.inl p)) = (x (S.xSlot p.1 p.2),x (S.ySlot p.1 p.2)) := rfl

/-- Cubic factor evaluation uses exactly the normal triple. -/
theorem inputFactorEquiv_normal (S : SumintShape) {α : Type*} (x : S.VIdx → α)
    (i : {i : Fin S.I // S.nor i = true}) (j : Fin 3) :
    inputFactorEquiv S α x (.inr (.inr i)) j = x (S.uSlot i.1 i.2 j) := rfl

end WaveTurbulence.SumintPar
