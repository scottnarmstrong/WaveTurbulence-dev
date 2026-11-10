/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VineExcess3`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 Vine removal, part 10 (FINALCOUNT-G2): **DH23 Prop 9.4, Step 1, single vine, conditional on `𝔉`** (L1797--L1801). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace VineCut
open WaveTurbulence.FinalCount.VineCut
variable {M : Molecule V D} (K : VineCut g M)

/-- `∏_{j : 𝕃_j ⊂ 𝕍ℂ} 𝔛_j^{z_j}` (L1799). -/
noncomputable def ladderProdVC (L γ δ : ℝ) (P : Finset V → ℝ) : ℝ :=
  ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S

theorem ladderProdVC_ge_one (L γ δ : ℝ) (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L) (hδ : 0 ≤ δ)
    (hP0 : ∀ S, 0 ≤ P S) : 1 ≤ K.ladderProdVC L γ δ P := by
  unfold ladderProdVC
  calc (1 : ℝ) = ∏ _S ∈ K.vc.maximalLadders, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one)
        (fun S _ => one_le_pow₀ (ladderWeight_ge_one L γ δ (P S) hL hδ (hP0 S)))

end VineCut
end WaveTurbulence.GammaLow.FinalCount.Step1
