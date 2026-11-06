/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamDirectedGraphIso
public import WaveTurbulenceVineParam.VineParamSpliceGeometry
import Mathlib.Tactic

/-! # Literal contracted graph with its two restored crossing occurrences -/

public section
namespace WaveTurbulence.Vine.Param
variable {V β : Type*} [DecidableEq V]

/-- Contracted old occurrences consist of the untouched bonds and two
individually marked restored crossing bonds. -/
@[expose] def contractedEnds (rest : β → V×V) (σ : V ≃ V)
    (p q c d : V) (P : RungPattern) : β ⊕ Fin 2 → V×V
  | .inl e => (σ.symm (rest e).1,σ.symm (rest e).2)
  | .inr j => ![orientPair (P.signs 2) p c,orientPair (-P.signs 2) q d] j

/-- The actual source cell retains the old physical atom names. -/
@[expose] def sourceCellEnds (rest : β → V×V) (p q c d : V) (P : RungPattern) :
    β ⊕ Fin 6 → (V ⊕ Fin 2)×(V ⊕ Fin 2)
  | .inl e => (.inl (rest e).1,.inl (rest e).2)
  | .inr j => ![orientPair (P.signs 2) (.inl p) (.inr 0),
      orientPair (-P.signs 2) (.inl q) (.inr 1),
      orientPair (P.signs 0) (.inr 0) (.inr 1),orientPair (P.signs 1) (.inr 0) (.inr 1),
      orientPair (P.signs 3) (.inr 0) (.inl c),orientPair (-P.signs 3) (.inr 1) (.inl d)] j

/-- Deleting both restored crossing occurrences leaves exactly the old
untouched bonds, with no occurrence choice. -/
@[expose] def contractedRestEquiv :
    {e : β ⊕ Fin 2 // e ≠ .inr 0 ∧ e ≠ .inr 1} ≃ β where
  toFun e := match e with
    | ⟨.inl e,_⟩ => e
    | ⟨.inr j,h⟩ => False.elim (by
      fin_cases j
      · exact h.1 rfl
      · exact h.2 rfl)
  invFun e := ⟨.inl e,by simp⟩
  left_inv := by
    rintro ⟨(e | j),h⟩
    · rfl
    · fin_cases j
      · exact (h.1 rfl).elim
      · exact (h.2 rfl).elim
  right_inv _ := rfl

/-- Re-expanding the contracted graph is exactly the original source cell,
including all separately marked parallel rung occurrences. -/
@[expose] def contractedSpliceIso [Fintype V] [Fintype β] [DecidableEq β]
    (rest : β → V×V) (σ : V ≃ V) (p q c d : V) (P : RungPattern) :
    DirectedGraphIso
      (rungSpliceEnds (contractedEnds rest σ p q c d P) (.inr 0) (.inr 1) σ p q c d P)
      (sourceCellEnds rest p q c d P) where
  atom := Equiv.refl _
  edge := Equiv.sumCongr contractedRestEquiv (Equiv.refl _)
  endpoints := by
    intro e
    cases e with
    | inl e =>
      rcases e with ⟨(e | j),h⟩
      · change (Sum.inl (rest e).1,Sum.inl (rest e).2)=
          (Sum.inl (σ (σ.symm (rest e).1)),Sum.inl (σ (σ.symm (rest e).2)))
        simp only [Equiv.apply_symm_apply]
      · fin_cases j
        · exact (h.1 rfl).elim
        · exact (h.2 rfl).elim
    | inr j => rfl

end WaveTurbulence.Vine.Param
