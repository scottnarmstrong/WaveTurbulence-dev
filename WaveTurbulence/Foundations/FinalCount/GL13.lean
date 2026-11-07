/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL12
public import WaveTurbulence.Foundations.FinalCount.G3Ghost
/-! **G3-LOWDEG (R48), part 13**: the dartless molecule (a single atom of degree `0`, Example A): `𝔄 ≤ 1`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **Degree `0` (R48 item 4, TARGET: Example A)**: a molecule without darts has `𝔈 ≤ 1`, `χ = 0` and no ladder, so `𝔄 ≤ 1`. -/
theorem countA_dartless_le_one [IsEmpty D] (M : Molecule V D) (L γ δ C₁ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) : M.countA L γ δ C₁ w Adm P ≤ 1 := by
  have hE : (M.countE L γ δ w Adm : ℝ≥0∞) ≤ 1 := by
    have h1 : M.countE L γ δ w Adm ≤ 1 := by
      unfold Molecule.countE
      refine iSup_le fun c => iSup_le fun _ => iSup_le fun β => iSup_le fun k0 => iSup_le fun _ => ?_
      refine Set.encard_le_one_iff.2 fun a b _ _ => ?_
      funext x; exact isEmptyElim x
    exact_mod_cast h1
  unfold Molecule.countA
  rw [dartless_rank M, dartless_ladders M]
  simpa using hE

end WaveTurbulence.FinalCountG3
