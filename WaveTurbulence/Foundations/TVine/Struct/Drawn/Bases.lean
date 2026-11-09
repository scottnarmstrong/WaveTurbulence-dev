/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Drawn.Cert

/-!
# The six drawn templates (III)–(VIII) with no inserted rungs are T-vines (packet L3D)

N2 Lemma 5.2, base (`research-gamma-half-2/NOTES.md` L833; M4 §8 F6). For each template `X`, the multigraph on
`range n` with the template's bonds (`tmplMS`) is a T-vine with joints `0, 1`: a block (degrees and a covering walk),
no multiplicity above `2`, and an explicit (Y2) path from the closure to the doubled triangle. All checks are kernel
evaluations (`decide +kernel`; no `native_decide`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Struct.Drawn

open TVine WaveTurbulence.TVine.Core

/-- The bond multiset of a template (undirected). -/
def tmplMS (T : VineTemplate) : Multiset (Sym2 ℕ) := ↑(T.bonds.map fun p => s(p.1, p.2))

/-- The template `III` (no inserted rungs) is a T-vine with joints `0, 1`. -/
theorem base_III : IsTVineU (ofMS (Finset.range 9) (tmplMS VineType.III.template)) 0 1 :=
  isTVineU_ofMS_of_cert _ _ 0 1 (by decide +kernel) (by decide) (by decide +kernel)
    [0, 2, 3, 5, 4, 6, 8, 1, 7] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {s(2, 3), s(7, 8)} (by decide +kernel)
    (Or.inl ⟨by decide +kernel, 2, 3, 7, 8, by decide +kernel, by decide +kernel, rfl⟩)
    (by decide +kernel) (by decide +kernel)
    [(2, 3, 4, 5), (7, 8, 4, 6)] {4, 5, 6} {s(4, 5), s(4, 5), s(5, 6), s(5, 6), s(4, 6), s(4, 6)}
    (by decide +kernel) 4 5 6 (by decide) (by decide) (by decide) rfl rfl

/-- The template `IV` (no inserted rungs) is a T-vine with joints `0, 1`. -/
theorem base_IV : IsTVineU (ofMS (Finset.range 9) (tmplMS VineType.IV.template)) 0 1 :=
  isTVineU_ofMS_of_cert _ _ 0 1 (by decide +kernel) (by decide) (by decide +kernel)
    [0, 2, 3, 6, 5, 4, 7, 1, 8] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {s(2, 3), s(7, 8)} (by decide +kernel)
    (Or.inl ⟨by decide +kernel, 2, 3, 7, 8, by decide +kernel, by decide +kernel, rfl⟩)
    (by decide +kernel) (by decide +kernel)
    [(2, 3, 4, 6), (7, 8, 4, 6)] {4, 5, 6} {s(4, 5), s(4, 5), s(5, 6), s(5, 6), s(4, 6), s(4, 6)}
    (by decide +kernel) 4 5 6 (by decide) (by decide) (by decide) rfl rfl

/-- The template `V` (no inserted rungs) is a T-vine with joints `0, 1`. -/
theorem base_V : IsTVineU (ofMS (Finset.range 9) (tmplMS VineType.V.template)) 0 1 :=
  isTVineU_ofMS_of_cert _ _ 0 1 (by decide +kernel) (by decide) (by decide +kernel)
    [0, 1, 3, 2, 4, 5, 7, 6, 8] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {s(2, 3)} (by decide +kernel)
    (Or.inr ⟨by decide +kernel, 2, 3, by decide +kernel, by decide +kernel, rfl⟩)
    (by decide +kernel) (by decide +kernel)
    [(2, 3, 4, 5), (4, 5, 6, 7)] {6, 7, 8} {s(6, 7), s(6, 7), s(7, 8), s(7, 8), s(6, 8), s(6, 8)}
    (by decide +kernel) 6 7 8 (by decide) (by decide) (by decide) rfl rfl

/-- The template `VI` (no inserted rungs) is a T-vine with joints `0, 1`. -/
theorem base_VI : IsTVineU (ofMS (Finset.range 15) (tmplMS VineType.VI.template)) 0 1 :=
  isTVineU_ofMS_of_cert _ _ 0 1 (by decide +kernel) (by decide) (by decide +kernel)
    [0, 2, 3, 5, 4, 6, 7, 9, 8, 10, 11, 12, 11, 10, 8, 9, 7, 14, 1, 13] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {s(2, 3), s(13, 14)} (by decide +kernel)
    (Or.inl ⟨by decide +kernel, 2, 3, 13, 14, by decide +kernel, by decide +kernel, rfl⟩)
    (by decide +kernel) (by decide +kernel)
    [(2, 3, 4, 5), (4, 5, 6, 8), (13, 14, 6, 7), (6, 7, 8, 9), (8, 9, 10, 11)] {10, 11, 12} {s(10, 11), s(10, 11), s(11, 12), s(11, 12), s(10, 12), s(10, 12)}
    (by decide +kernel) 10 11 12 (by decide) (by decide) (by decide) rfl rfl

/-- The template `VII` (no inserted rungs) is a T-vine with joints `0, 1`. -/
theorem base_VII : IsTVineU (ofMS (Finset.range 11) (tmplMS VineType.VII.template)) 0 1 :=
  isTVineU_ofMS_of_cert _ _ 0 1 (by decide +kernel) (by decide) (by decide +kernel)
    [0, 2, 3, 8, 6, 4, 5, 7, 9, 1, 10] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {s(2, 3), s(9, 10)} (by decide +kernel)
    (Or.inl ⟨by decide +kernel, 2, 3, 9, 10, by decide +kernel, by decide +kernel, rfl⟩)
    (by decide +kernel) (by decide +kernel)
    [(2, 3, 7, 8), (9, 10, 7, 8), (7, 8, 5, 6)] {4, 5, 6} {s(4, 5), s(4, 5), s(5, 6), s(5, 6), s(4, 6), s(4, 6)}
    (by decide +kernel) 4 5 6 (by decide) (by decide) (by decide) rfl rfl

/-- The template `VIII` (no inserted rungs) is a T-vine with joints `0, 1`. -/
theorem base_VIII : IsTVineU (ofMS (Finset.range 11) (tmplMS VineType.VIII.template)) 0 1 :=
  isTVineU_ofMS_of_cert _ _ 0 1 (by decide +kernel) (by decide) (by decide +kernel)
    [0, 2, 3, 5, 1, 4, 1, 5, 3, 7, 6, 8, 9, 10] (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {s(2, 6), s(4, 5)} (by decide +kernel)
    (Or.inl ⟨by decide +kernel, 2, 6, 4, 5, by decide +kernel, by decide +kernel, rfl⟩)
    (by decide +kernel) (by decide +kernel)
    [(4, 5, 2, 3), (2, 3, 6, 7), (6, 7, 8, 9)] {8, 9, 10} {s(8, 9), s(8, 9), s(9, 10), s(9, 10), s(8, 10), s(8, 10)}
    (by decide +kernel) 8 9 10 (by decide) (by decide) (by decide) rfl rfl

end WaveTurbulence.TVine.Struct.Drawn
