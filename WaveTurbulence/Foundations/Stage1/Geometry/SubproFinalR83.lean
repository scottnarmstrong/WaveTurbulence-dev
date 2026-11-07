/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
-- R83 port of sp-src/SubproFinal.lean (FLOWER-P6 R83): successor designations, see HANDOFF

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproCross3R83
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSupportAR83
public import WaveTurbulence.Foundations.FinalCount.SubproTame
import Mathlib.Tactic

/-!
# SUBPRO (S4): TARGET Prop `subpro` (L2040-L2051) for the construction of S2a (R28, atom-set form)

`subproSupportA`: on the support of the epsilon and gap factors, `SubproSupportA` (the six conclusions of `subpro`, with
`contained` and `crossing` in the atom-set form of TARGET's "subset", R28 ruling 3) holds for `G_sb`, `C_1`, the hinges and
the hinge pairs of `stage1PieceOf`.  `SubproObligationA` is the atom-set version of `RedSplice.SubproObligation`;
`subproObligationA` discharges it (needs `P.L ≠ 0`, R28 ruling 4).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

variable {R : ℕ} {G : Garden (2 * R)}

/-- **`subpro` (2)-(6) for the construction, for one decoration.** -/
theorem subproSupportA (σ : Prescription G) {d : ℕ}
    (D : SplicedKernelData (stSt G σ).G d) (hD : D.gapSpecification = gapSpecification G σ)
    (hpl : (stSt G σ).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (stSt G σ).G d roots 0)
    (hε : splicedEpsilon (stSt G σ).G (collectionChoices G σ).hinges z.1 ≠ 0)
    (hZ : splicedGapIndicator (stSt G σ).G D L γ η base z.1 ≠ 0) :
    SubproSupportA (stSt G σ).G (collectionChoices G σ) L γ η base
      (Finset.univ.image (fun i => base + latticePoint L (roots i))) (bondIndex (stSt G σ).G z.1) := by
  have hdec := sbDec_of_gen σ hpl hL base roots z
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  refine ⟨selectedSG_cc2 σ D hD L γ η base z.1 hZ hdec, ?_, contained_support σ D hD L γ η base z.1 hZ,
    hingeSG_cc2 σ D hD L γ η base z.1 hZ hdec, hingeJoint_cc2 σ, ?_⟩
  · intro v hv hg
    exact tame_of_eps (stSt G σ).G hpl hL base roots z hε hv hg
  · intro P _ hout hnd
    have hout' : ∀ O ∈ objects G σ, ¬ P.atoms ⊆ O.atoms := by
      intro O hO
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hO
      have := hout i
      simp only [collectionChoices] at this
      rw [hi] at this
      exact this
    exact crossing_atoms hM σ P hout' hnd

end WaveTurbulence.VineA.NormalizedSplice.Subpro
