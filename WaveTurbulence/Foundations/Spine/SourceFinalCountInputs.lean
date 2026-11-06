/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
public import WaveTurbulence.Foundations.Spine.AnchorTypes
/-! TARGET finalcount1, L2114–L2116, as a separate conditional source input.
The epsilon/gap support and requirements (a)–(f) are explicit. The disputed
lgmolect/rigidity step is upstream of this input, never hidden in another gate. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped ENNReal

/-- Literal (k1,...,k2R)-decorations of the normalized spliced kernel satisfying source
requirements (b)–(f). Requirement (a), including the fixed unit balls and energy windows,
is inside the literal Molecule.countE used below. The actual epsilon/gap support is retained;
replacing it by only its subpro consequences would produce a stronger, incorrect count. -/
def splicedCountingAdmissible {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (C : SourceVine.CountingChoices G d) (L γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (κ : GardenDart G → (Fin d → ℤ)) : Prop :=
  (∃ z : GenDecoration G d roots 0, (∀ x, bondIndex G z.1 x = κ x) ∧
    splicedEpsilon G D.hinges z.1 ≠ 0 ∧ splicedGapIndicator G D L γ η base z.1 ≠ 0) ∧
  C.Admissible L γ η base κ

/-- TARGET finalcount1 (L2114–L2116), including its literal normalized countA from defcounta.
Standing data are the actual spliced garden, subpro geometry, source collections C1/C2,
the fixed SG atom choices, and the dyadic ladder/atom scales in (a)–(f). Provider: F3 FINAL-COUNT;
G8 RIGID (lgmolect/finalcount) and G3 EXCESS-T are upstream. This is kept separate because of
F69b's disputed T-necklace regime gamma ≤ 1/2. No norm of a garden or kernel is assumed. -/
abbrev FinalCountGate : Prop := WTPrefix fun P =>
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (C : SourceVine.CountingChoices G P.d),
    D.hinges = C.subpro.hinges → SourceVine.CountingGeometry G C →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ Adm : (GardenDart G → (Fin P.d → ℤ)) → Prop,
    (∀ κ, Adm κ → splicedCountingAdmissible G D C P.L P.γ P.η base roots κ) →
    G.molecule.countA P.L P.γ P.δ P.C₁ base Adm C.ladderScale ≤
      ENNReal.ofReal
        (P.L ^ (-4 * P.η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          P.L ^ (((R : ℝ) - 1) * ((P.d : ℝ) - P.γ - 1 / 4 - 1 / 40)))

end WaveTurbulence.LGSpine
