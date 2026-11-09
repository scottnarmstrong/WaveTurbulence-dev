/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew6
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew5
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCNew6`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 28 (session 4): from the new-component count to the deviation `I ≲ L^{γ₀} · excessRHS L γ η [] 1 2`
(TARGET excessprop1 (2), (excesseqn2+), L2167--L2177). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- `Δχ`: removing a vine that creates one new component lowers the circuit rank by `m - 1`. -/
theorem circuitRank_diff_new {M : Molecule V D} (K : VineCut g M) (hF : K.post.numComponents = M.numComponents + 1)
    (hB : K.vc.bonds.card = 2 * (K.C.atoms.card - 1)) (hm : 1 ≤ K.C.atoms.card) :
    M.circuitRank - K.post.circuitRank = ((K.C.atoms.card - 1 : ℕ) : ℤ) := by
  have h := K.circuitRank_diff
  have h2 : K.vc.circuitRank = (K.vc.bonds.card : ℤ) - K.vc.atoms.card + K.vc.numComponents := rfl
  rw [h2, K.vc_atoms_card, hB, hF] at h
  rw [h]
  have : ((2 * (K.C.atoms.card - 1) : ℕ) : ℤ) = 2 * (K.C.atoms.card : ℤ) - 2 := by
    push_cast [Nat.cast_sub hm]; ring
  rw [this]
  push_cast [Nat.cast_sub hm]
  ring

end WaveTurbulence.GammaLow.FinalCount.Step1
