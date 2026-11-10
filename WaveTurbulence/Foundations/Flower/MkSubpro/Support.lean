/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSubpro.Survivors
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSupportMK

/-! # B2c MK-SUBPRO (world side), part 2: Theorem 7.5′ (2), (4)–(6′) as the world's `SubproSupportMK`

`subproSupportMK_survData`: on one decoration of the support of the marked splice, the world's
`FinalMKDefs.SubproSupportMK` holds for `𝒞₁ = collectionChoices G σ Mk` and the survivors `survData G σ Mk prot`.
It is main's `subproSupportMKAt` (B2c, Stage1/Geometry/SubproSupportMK), whose fields are the world's with the survivor
family spelled out.  Ruling R173: `hMkSG : Mk ⊆ vinesV0 G σ` (every marked vine lies in an SG group), supplied by B4.
-/

@[expose] public section
set_option autoImplicit false

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset
open WaveTurbulence.RedSplice (Prescription stSt vinesV0 survivorsMk)

namespace WaveTurbulence.Flower.MkSubpro
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

variable {w : ℕ}

/-- **o75 Theorem 7.5′ (2), (4), (5) with 75-F1, (6), (6′)** for the marked splice, as the world's
`SubproSupportMK`, on one decoration of the support of the epsilon and gap factors. -/
theorem subproSupportMK_survData {R : ℕ} {G : Garden (2 * R)} (σ : Prescription G) {Mk : Set (Stage1.CLVine G)}
    (hMkSG : Mk ⊆ vinesV0 G σ) {d : ℕ} (D : SplicedKernelData (stSt G σ Mk).G d)
    (hD : D.gapSpecification = VineA.NormalizedSplice.gapSpecificationMk G σ Mk)
    (hpl : (stSt G σ Mk).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (stSt G σ Mk).G d roots 0)
    (hε : splicedEpsilon (stSt G σ Mk).G (VineA.NormalizedSplice.collectionChoices G σ Mk).hinges z.1 ≠ 0)
    (hZ : splicedGapIndicator (stSt G σ Mk).G D L γ η base z.1 ≠ 0)
    (prot : Finset (GBranch (stSt G σ Mk).G.tree)) :
    SubproSupportMK (stSt G σ Mk).G (VineA.NormalizedSplice.collectionChoices G σ Mk) (survData G σ Mk prot)
      L γ η base (Finset.univ.image (fun i => base + latticePoint L (roots i))) (bondIndex (stSt G σ Mk).G z.1) :=
  have h := VineA.NormalizedSplice.Subpro.subproSupportMKAt σ hMkSG D hD hpl hL γ η base roots z hε hZ
  ⟨h.selectedSG, h.survivorSG, h.zeroTame, h.contained, h.hingeSG, h.hingeJoint, h.jointPair, h.crossing,
    h.meetB⟩

end WaveTurbulence.Flower.MkSubpro
