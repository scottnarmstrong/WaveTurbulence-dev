/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapPrefixData
import Mathlib.Tactic

/-! # Distinctness of a cap family from a full rail frame -/

public section
namespace WaveTurbulence.Vine

/-- Index the triangle and all noninitial rail atoms in a full frame. -/
@[expose] def capFullIndex (n : ℕ) : CapIndex (n+1) → Option (Fin (n+2) ⊕ Fin (n+2))
  | .inl i => if i=0 then none else if i=1 then some (.inl 0) else some (.inr 0)
  | .inr (.inl i) => some (.inl ⟨i.1+1,by omega⟩)
  | .inr (.inr i) => some (.inr ⟨i.1+1,by omega⟩)

/-- The frame index keeps every triangle and rail coordinate distinct. -/
theorem capFullIndex_injective (n : ℕ) : Function.Injective (capFullIndex n) := by
  intro i j he
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  · fin_cases i <;> fin_cases j <;> simp_all [capFullIndex]
  · fin_cases i <;> simp_all [capFullIndex]
  · fin_cases i <;> simp_all [capFullIndex]
  · fin_cases j <;> simp_all [capFullIndex]
  · simp only [capFullIndex,Option.some.injEq,Sum.inl.injEq,Fin.mk.injEq] at he
    have : i=j := Fin.ext (by omega)
    exact congrArg (Sum.inr ∘ Sum.inl) this
  · simp [capFullIndex] at he
  · fin_cases j <;> simp_all [capFullIndex]
  · simp [capFullIndex] at he
  · simp only [capFullIndex,Option.some.injEq,Sum.inr.injEq,Fin.mk.injEq] at he
    have : i=j := Fin.ext (by omega)
    exact congrArg (Sum.inr ∘ Sum.inr) this

/-- Primitive distinctness of both complete rails, including both ports,
and separation of the triangular center imply cap-family distinctness. -/
theorem capAtomFamily_injective_of_full_frame {V : Type*} (center : V)
    (u v : ℕ → V) (n : ℕ)
    (hd : Function.Injective (Sum.elim (fun i : Fin (n+2) => u i.1)
      (fun i : Fin (n+2) => v i.1)))
    (hc : ∀ i,i ≤ n+1 → center ≠ u i ∧ center ≠ v i) :
    Function.Injective (capAtomFamily center (u 0) (v 0) u v (n+1)) := by
  let F : Option (Fin (n+2) ⊕ Fin (n+2)) → V :=
    fun i => match i with
    | none => center
    | some (.inl j) => u j.1
    | some (.inr j) => v j.1
  have hF : Function.Injective F := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        cases j with
        | inl j => exact False.elim ((hc j.1 (by omega)).1 he)
        | inr j => exact False.elim ((hc j.1 (by omega)).2 he)
    | some i =>
      cases j with
      | none =>
        cases i with
        | inl i => exact False.elim ((hc i.1 (by omega)).1 he.symm)
        | inr i => exact False.elim ((hc i.1 (by omega)).2 he.symm)
      | some j =>
        congr 1
        apply hd
        cases i <;> cases j <;> exact he
  have hf : capAtomFamily center (u 0) (v 0) u v (n+1)=F ∘ capFullIndex n := by
    funext i
    rcases i with i | (i | i)
    · fin_cases i <;> rfl
    · rfl
    · rfl
  rw [hf]
  exact hF.comp (capFullIndex_injective n)

end WaveTurbulence.Vine
