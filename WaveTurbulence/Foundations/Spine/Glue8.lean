/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue7
public import WaveTurbulence.Foundations.Spine.KLemma
import Mathlib.Tactic
/-! The sets `S_v` containing the `α_v` (TARGET L2025–L2026) with the `K`-lemma bound. -/
@[expose] public section
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

/-- The volume bound `M_v = 2 (⌊2L⌋₊ + 1)^{4d}` for the sets `S_v`. -/
noncomputable def Mv (d : ℕ) (L : ℝ) : ℝ := 2 * ((⌊2 * L⌋₊ + 1 : ℕ) : ℝ) ^ (4 * d)

theorem one_le_Mv (d : ℕ) {L : ℝ} (_hL : 0 ≤ L) : 1 ≤ Mv d L := by
  unfold Mv
  have : (1 : ℝ) ≤ ((⌊2 * L⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have h2 := one_le_pow₀ (n := 4 * d) this
  linarith

theorem exists_Sy (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d)
    (hamp : SplicedAmplitudeBounds G D) (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    ∃ Sy : GBranch G.tree → Set ℝ, (∀ b, MeasurableSet (Sy b)) ∧
      (∀ b (β : ℝ), ∫⁻ a in Sy b, ENNReal.ofReal (br (a + β))⁻¹ ≤ ENNReal.ofReal (2 * Real.arsinh (Mv d L) + 1)) ∧
      ∀ α ∈ splicedFrequencySpectrum G D scales L γ η δ base roots, ∀ α' : GBranch G.tree → ℝ, (∀ b, |α' b - α b| ≤ 1) →
        ∀ b, α' b ∈ Sy b := by
  have h1 := fun b => exists_value_finset G hp hL D hamp scales γ η δ base roots b
  choose F hF hFc using h1
  refine ⟨fun b => ⋃ a ∈ F b, Set.Icc (a - 1) (a + 1), fun b => ?_, fun b β => ?_, ?_⟩
  · exact Finset.measurableSet_biUnion _ (fun a _ => measurableSet_Icc)
  · refine lintegral_br_inv_le (Finset.measurableSet_biUnion _ (fun a _ => measurableSet_Icc))
      (one_le_Mv d hL.le) ?_ β
    calc volume (⋃ a ∈ F b, Set.Icc (a - 1) (a + 1))
        ≤ ∑ a ∈ F b, volume (Set.Icc (a - 1) (a + 1)) := measure_biUnion_finset_le _ _
      _ = ∑ _a ∈ F b, ENNReal.ofReal 2 := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Real.volume_Icc]; congr 1; ring
      _ = ((F b).card : ℝ≥0∞) * ENNReal.ofReal 2 := by simp
      _ = ENNReal.ofReal (2 * (F b).card) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]; ring
      _ ≤ ENNReal.ofReal (Mv d L) := by
          apply ENNReal.ofReal_le_ofReal
          unfold Mv
          have : ((F b).card : ℝ) ≤ ((⌊2 * L⌋₊ + 1 : ℕ) : ℝ) ^ (4 * d) := by exact_mod_cast hFc b
          linarith
  · intro α hα α' hclose b
    simp only [Set.mem_iUnion]
    refine ⟨α b, hF b α hα, ?_⟩
    have := abs_le.mp (hclose b)
    constructor <;> linarith [this.1, this.2]

end WaveTurbulence.Ladder
