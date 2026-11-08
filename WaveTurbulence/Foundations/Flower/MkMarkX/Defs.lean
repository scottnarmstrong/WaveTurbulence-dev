/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.BatchSel
public import WaveTurbulence.Foundations.Flower.MkMark.StemZero

/-! # B2e MK-X: the stem-unclean marking `X` and the fine marking `markIX = markI ∪ X` (R177, F-B4-4 (b))

* `markX J A`: the vines of `𝒱` whose twist-active set `𝐀(𝕍)` meets the capped stem (stem-unclean vines;
  `activeSet` depends only on the atoms and the upper joint of the vine).
* `markIX J pat t s kSel A := markI J pat t s kSel A ∪ markX J A`: B4's fine′ marking `mkF`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Stage1

namespace WaveTurbulence.Flower.MkMarkX

variable {w : ℕ}

/-- **The stem-unclean marking `X`** (R177): the vines of `𝒱` whose twist-active set meets the capped stem. -/
def markX (J : Finset (Fin w)) : MarkFn w :=
  fun A => {c | c ∈ vinesV A.skeleton ∧ ¬ StemCleanAt J A c.atoms c.upper}

/-- **The fine′ marking `mkF = markI ∪ X`** (R177, F-B4-4 (b)). -/
def markIX (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ) : MarkFn w :=
  fun A => markI J pat t s kSel A ∪ markX J A

theorem mem_markX_iff (J : Finset (Fin w)) {LG : LayeredGarden w} (A : VineA.PrimeData LG)
    (c : CLVine A.skeleton) :
    c ∈ markX J A ↔ c ∈ vinesV A.skeleton ∧ ¬ StemCleanAt J A c.atoms c.upper := Iff.rfl

theorem mem_markIX_iff (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    {LG : LayeredGarden w} (A : VineA.PrimeData LG) (c : CLVine A.skeleton) :
    c ∈ markIX J pat t s kSel A ↔ c ∈ markI J pat t s kSel A ∨ c ∈ markX J A := Iff.rfl

theorem markIX_subset_vinesV (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    {LG : LayeredGarden w} (A : VineA.PrimeData LG) : markIX J pat t s kSel A ⊆ vinesV A.skeleton := by
  rintro c (hc | hc)
  · exact hc.1
  · exact hc.1

end WaveTurbulence.Flower.MkMarkX
