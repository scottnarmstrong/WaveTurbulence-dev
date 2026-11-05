/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapIndices
import Mathlib.Tactic

/-! # Distinctness labels for a triangle, a fresh ladder, and two old far ports -/

public section
namespace WaveTurbulence.Vine

/-- A triangle4,5,6, two far ports7,8, and k fresh paired rail atoms.
The last coordinate of each rail index family names its far port. -/
@[expose] def capEndpointLabel (N k : ℕ) : CapIndex (k+1) → ℕ
  | .inl i => 4+i.1
  | .inr (.inl i) => if i.1=k then 7 else N+i.1
  | .inr (.inr i) => if i.1=k then 8 else N+k+i.1

/-- Old ports and fresh interior labels are all distinct. -/
theorem capEndpointLabel_injective (N k : ℕ) (hN : 9 ≤ N) :
    Function.Injective (capEndpointLabel N k) := by
  intro i j he
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (Fin.ext (by change 4+i.1=4+j.1 at he; omega))
    | inr j =>
      cases j <;> dsimp only [capEndpointLabel] at he <;> split_ifs at he <;> omega
  | inr i =>
    cases i with
    | inl i =>
      cases j with
      | inl j => dsimp only [capEndpointLabel] at he; split_ifs at he <;> omega
      | inr j =>
        cases j with
        | inl j =>
          apply congrArg (Sum.inr ∘ Sum.inl)
          apply Fin.ext
          dsimp only [capEndpointLabel] at he
          split_ifs at he <;> omega
        | inr j =>
          dsimp only [capEndpointLabel] at he
          split_ifs at he <;> omega
    | inr i =>
      cases j with
      | inl j => dsimp only [capEndpointLabel] at he; split_ifs at he <;> omega
      | inr j =>
        cases j with
        | inl j =>
          dsimp only [capEndpointLabel] at he
          split_ifs at he <;> omega
        | inr j =>
          apply congrArg (Sum.inr ∘ Sum.inr)
          apply Fin.ext
          dsimp only [capEndpointLabel] at he
          split_ifs at he <;> omega

end WaveTurbulence.Vine
