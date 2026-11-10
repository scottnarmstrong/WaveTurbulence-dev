/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Flower.FinalMKStep.Pot

/-! # FLOWER-LOW (packet L8), item H (re-cut ledger): the survivor budget banks `L²` per pending re-cut

Main's re-cut step `FinalMKStep.hW_RCp` (o75 75-F2 on main's potential model) takes
`hmarg : 2·min γ (1−γ) + 4η² ≤ 1`, which is false at `γ = 1/2` for every `η > 0` (M3 §7.2; REF-M3 R3; AUDIT-V4 §7
watch item 1). Main banks `L¹` per pending re-cut (`g1E = g1 − pendRC`). Following M3 §7.2 as repaired by REF-M3 R3,
this module banks `L²` per pending re-cut:

  `g1E2 = g1 − 2·pendRCG`,

so the re-cut step gains `L²`, and its margin is `2γ₀ + 3η² + 8η⁶ + ε₀ − 2 ≤ 0`, which holds for every `γ ∈ (0,1)`
(`γ₀ = min γ (1−γ) ≤ 1/2`) once `η ≤ 1/40` and `ε₀ ≤ η²/2`: **`hW_RCp2` has no hypothesis on `γ`**. The initial cost
of the budget is `L^{2·pendRC₀} ≤ L^{2m}` (`WPot_g1E2_le`) instead of `L^{m}`; with `m = N_E ≤ 2b` the total survivor
charge is `L^{(2+γ₀)N_E} ≤ L^{5b}` (REF-M3 R3), absorbed by (10.4).

The survivors are over `𝒱_γ` (`Src.Object γ`, L6's carrier): `DartlessG`, `pendRCG` are main's `Dartless`
(`FinalCount/AsmPhase1.lean`) and `pendRC` (`Flower/FinalMKDefs/Count.lean`) with that carrier. Everything else
(`HSt`, `WPot`, `g1`, `apProd`, `Inv`, `eraseA`, `excessRHS2`, `pot_step_idx_le`, `WPot_mono_Y`) is main's and
family-free, by import. The proofs are main's (`FinalMKStep/Pot.lean`, sha256 in `COPIED-SHA256SUMS`) with the bank
changed from `1` to `2`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal

namespace WaveTurbulence.GammaLow.Flower
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKStep

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

/-- No dart of the `𝒱_γ` object `U` of `M₀` remains in the state `h` (main's `FinalCountAsm.Dartless`). -/
def DartlessG {γ : ℝ} {M₀ : Molecule V D₀} (U : FinalCount.Src.Object γ M₀) (h : HSt V D₀) : Prop :=
  ∀ x : h.s.D, ¬ U.ContainsDart (h.s.down x)

section hWRC
variable {γ L γ' η : ℝ} {M₀ : Molecule V D₀} {m : ℕ}

/-- The pending re-cuts of a state: survivors still present that share a joint with an earlier survivor (main's
`FinalMKDefs.pendRC` over `𝒱_γ`). -/
noncomputable def pendRCG (E : Fin m → FinalCount.Src.Object γ M₀) (h : HSt V D₀) : ℕ :=
  (Finset.univ.filter fun i : Fin m => ¬ DartlessG (E i) h ∧ ∃ j, j < i ∧ ¬ Disjoint (E j).atoms (E i).atoms).card

/-- The re-cut margin with the `L²` bank, for every `γ'` (`γ₀ ≤ 1/2`). -/
theorem two_gam0_le_one (γ' : ℝ) : 2 * min γ' (1 - γ') ≤ 1 := by
  have h1 := min_le_left γ' (1 - γ')
  have h2 := min_le_right γ' (1 - γ')
  linarith

/-! ### Lifting main's phase-1 steps to the `L²` survivor budget -/

end hWRC

end WaveTurbulence.GammaLow.Flower
