/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapBijection
public import WaveTurbulence.Foundations.Molecule.VineFamilyAtomLabels
import Mathlib.Tactic

/-! # Finite triangle-cap indices and their literal natural labels -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- The three triangle atoms, the upper full rungs and the lower full rungs. -/
abbrev CapIndex (r : ℕ) := Fin 3 ⊕ (Fin r ⊕ Fin r)

/-- The literal graph labels of a cap index. -/
@[expose] def capIndexLabel (N r : ℕ) : CapIndex r → ℕ
  | .inl i => 4+i.1
  | .inr (.inl i) => N+i.1
  | .inr (.inr i) => N+r+i.1

/-- The triangle and the two rail allocations are disjoint label families. -/
theorem capIndexLabel_injective (N r : ℕ) (hN : 9 ≤ N) :
    Function.Injective (capIndexLabel N r) := by
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact congrArg Sum.inl (Fin.ext (by change 4+i.1=4+j.1 at he; omega))
    | inr j =>
      cases j <;> dsimp only [capIndexLabel] at he <;> omega
  | inr i =>
    cases i with
    | inl i =>
      cases j with
      | inl j => dsimp only [capIndexLabel] at he; omega
      | inr j =>
        cases j with
        | inl j =>
          exact congrArg (Sum.inr ∘ Sum.inl) (Fin.ext (by change N+i.1=N+j.1 at he; omega))
        | inr j => dsimp only [capIndexLabel] at he; omega
    | inr i =>
      cases j with
      | inl j => dsimp only [capIndexLabel] at he; omega
      | inr j =>
        cases j with
        | inl j => dsimp only [capIndexLabel] at he; omega
        | inr j =>
          exact congrArg (Sum.inr ∘ Sum.inr) (Fin.ext (by change N+r+i.1=N+r+j.1 at he; omega))

/-- The index family has exactly the literal cap's available labels. -/
theorem capIndexLabel_image (N r : ℕ) :
    (univ : Finset (CapIndex r)).image (capIndexLabel N r)=capLabels N r := by
  ext a
  rw [mem_capLabels_iff]
  constructor
  · intro ha
    obtain ⟨i,_hi,rfl⟩ := mem_image.mp ha
    cases i with
    | inl i => fin_cases i <;> norm_num [capIndexLabel]
    | inr i => cases i <;> dsimp only [capIndexLabel] <;> omega
  · intro ha
    rcases ha with rfl | rfl | rfl | ⟨hlo,hhi⟩
    · exact mem_image.mpr ⟨.inl 0,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨.inl 1,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨.inl 2,mem_univ _,rfl⟩
    · by_cases hu : a<N+r
      · refine mem_image.mpr ⟨.inr (.inl ⟨a-N,by omega⟩),mem_univ _,?_⟩
        dsimp only [capIndexLabel]
        omega
      · refine mem_image.mpr ⟨.inr (.inr ⟨a-(N+r),by omega⟩),mem_univ _,?_⟩
        dsimp only [capIndexLabel]
        omega

end WaveTurbulence.Vine
