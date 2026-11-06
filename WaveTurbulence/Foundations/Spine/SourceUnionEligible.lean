/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.Spine.SourceUnionNotVine
/-! Eligibility of the union of two selected ordinary objects meeting at one joint, when one of
them lies in an ordinary LG/ZG container; and the union is never an omitted atom set. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem object_vc_hasGapKind_iff (O : Object M) (h : ∃ h, O.shape = .vc h) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (k : Molecule.GapKind) :
    O.HasGapKind L γ η w κ k ↔
      ∃ r, M.IsBlockGap L w κ O.atoms O.upper r ∧ Molecule.gapKind L γ η r = k := by
  obtain ⟨hh, hs⟩ := h
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h' => exact Iff.rfl
  | hyper R => cases hs

theorem object_vc_block (O : Object M) (h : ∃ h, O.shape = .vc h) :
    M.IsBlock O.atoms O.upper O.lower := by
  obtain ⟨hh, hs⟩ := h
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h' => exact h'.1
  | hyper R => cases hs

theorem object_contained_of_vc_subset (U C : Object M) (hU : ∃ h, U.shape = .vc h)
    (hsub : U.atoms ⊆ C.atoms) : U.IsContained C := by
  obtain ⟨hh, hs⟩ := hU
  rcases U with ⟨A, x, y, Ush⟩
  rcases C with ⟨S, a, b, Csh⟩
  cases Ush with
  | vc h' => cases Csh <;> exact hsub
  | hyper R => cases hs

end WaveTurbulence.LGSpine
