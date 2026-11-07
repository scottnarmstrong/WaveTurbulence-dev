/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproFinal
import Mathlib.Tactic

/-!
# SUBPRO (S4): the discharge of the S4 obligation of `stage1PieceOf` (atom-set form, R28)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open TTree Finset WaveTurbulence WaveTurbulence.Mole WaveTurbulence.LGSpine WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RedSplice WaveTurbulence.LGSpine.SourceVine

variable {R : ℕ}

/-- The atom-set version of `RedSplice.SubproObligation` (`SubproSupport` with atom-set `contained` and `crossing`). -/
@[expose] def SubproObligationA {P : WTParams} (π : Stage1Piece P R) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) : Prop :=
  ∀ z : GenDecoration π.Gsb P.d roots 0,
    splicedEpsilon π.Gsb π.Cs.hinges z.1 ≠ 0 →
    splicedGapIndicator π.Gsb (π.data (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)) P.L P.γ P.η base z.1 ≠ 0 →
    SubproSupportA π.Gsb π.Cs P.L P.γ P.η base
      (Finset.univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex π.Gsb z.1)

/-- **S4 discharged (atom-set form):** `SubproObligationA` holds for the Stage 1 piece of the construction. -/
theorem subproObligationA (P : WTParams) {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (hP : IsPrimeGarden S) (hI : S.Irreducible) (hbal : IsBalancedSig S.sig) (hn : 1 ≤ S.order)
    (p : ℕ) (hN : S.order ≤ P.N (p + 1) ^ 4) (hlayer : ∀ v, RegRed.coreLayer LG D hS hd v ≤ p)
    (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) :
    SubproObligationA (stage1PieceOf P.d hS LG hd σ) base roots := by
  obtain ⟨hB, -, -⟩ := construction_facts S hP hI hbal hn σ (RegRed.coreLayer LG D hS hd) p (P.N (p + 1) ^ 4) hN hlayer
  intro z hε hZ
  exact subproSupportA σ _ rfl hB.plain hL P.γ P.η base roots z hε hZ

end WaveTurbulence.Subpro
