/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproFinal2
public import WaveTurbulence.Foundations.FinalCount.RedSplicePiece
import Mathlib.Tactic

/-!
# S2 REPRESENTS: Stage 1 glue (S4's atom-set `SubproSupportA` is lg-spine-u's `SubproSupport`)

`supportOfA` converts S4's `SubproSupportA` to lg-spine-u's AMEND2 `SourceVine.SubproSupport` field by field
(all six fields agree textually; `OutsideAtoms C P` unfolds to `∀ i, ¬ P.atoms ⊆ (C.collection i).atoms`).
`stage1Piece_sound_uncond` is `RedSplice.stage1Piece_sound` with the `SubproObligation` discharged by
`Subpro.subproObligationA` (needs `P.L ≠ 0`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Represents
open TTree Finset WaveTurbulence WaveTurbulence.Mole WaveTurbulence.LGSpine WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine.SourceVine WaveTurbulence.RedSplice
  WaveTurbulence.Subpro WaveTurbulence.Reg

variable {R : ℕ}

theorem supportOfA {w d : ℕ} {G : Garden w} {C : SubproChoices G} {L γ η : ℝ} {base : Mom d}
    {kFix : Finset (Mom d)} {κ : GardenDart G → (Fin d → ℤ)}
    (h : SubproSupportA G C L γ η base kFix κ) : SubproSupport G C L γ η base kFix κ :=
  ⟨h.selectedSG, h.zeroTame, h.contained, h.hingeSG, h.hingeJoint, h.crossing⟩

theorem subproObligation_of_A {P : WTParams} (π : Stage1Piece P R) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : SubproObligationA π base roots) :
    SubproObligation π base roots :=
  fun z h1 h2 => supportOfA (h z h1 h2)

/-- `Stage1Piece.Sound` for the construction, unconditionally (S4 discharges the subpro obligation). -/
theorem stage1Piece_sound_uncond (P : WTParams) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (hP : IsPrimeGarden S) (hI : S.Irreducible) (hbal : IsBalancedSig S.sig) (hn : 1 ≤ S.order)
    (p : ℕ) (hN : S.order ≤ P.N (p + 1) ^ 4) (hlayer : ∀ v, RegRed.coreLayer LG D hS hd v ≤ p)
    (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    Stage1Piece.Sound (P := P) (stage1PieceOf P.d hS LG hd σ) p base roots :=
  stage1Piece_sound P hS LG hd σ hP hI hbal hn p hN hlayer base roots
    (subproObligation_of_A _ base roots
      (subproObligationA P hS LG hd σ hP hI hbal hn p hN hlayer hL base roots))

end WaveTurbulence.Represents
