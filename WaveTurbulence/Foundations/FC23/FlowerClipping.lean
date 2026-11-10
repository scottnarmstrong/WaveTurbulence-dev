/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FC23.FlowerExtraction
public import WaveTurbulence.Foundations.XChain.ClippedInputs
/-! Actual canonical flower carriers only see inputs at layers at most p. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.FC23
open Induct
variable (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

theorem flowerWeighted_clip
    (weight : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) :
    flowerWeighted P (inputsF P (clipRemainder p R)) p N kind pat dagger weight ζ t s n n' =
    flowerWeighted P (inputsF P R) p N kind pat dagger weight ζ t s n n' := by
  unfold flowerWeighted
  refine finsum_congr fun LG => finsum_congr fun h => ?_
  have he (a : GNode LG.garden.tree) :
      inputsF P (clipRemainder p R) (LG.layer a) = inputsF P R (LG.layer a) :=
    inputsF_clip_eq P R (Canon.layer_le_of_isCanonH h.1 a)
  unfold kernelKgen
  simp only [he]

end WaveTurbulence.FC23
