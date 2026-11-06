/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
public import WaveTurbulence.Foundations.Spine.SourceSplicedFourier
/-! A fixed time-frequency box gives the exact molecular energy windows of countE. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Mole

noncomputable def splicedEnergyCenter {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (σ : GBranch G.tree → ℤ) : GBranch G.tree → ℝ :=
  fun v => gardenSource G hp (fun i => ‖base + latticePoint L (roots i)‖ ^ 2) v +
    (D.frequency v - σ v) / (δ * L ^ (2 * γ))

theorem spliced_energy_residual {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (γ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (σ : GBranch G.tree → ℤ) (z : GenDecoration G d roots 0) (v : GBranch G.tree) :
    (G.molecule.Gamma L base (bondIndex G z.1) v - splicedEnergyCenter G hp D L γ δ base roots σ v) *
      (δ * L ^ (2 * γ)) = σ v - splicedFrequency G D L γ δ base z.1 v := by
  rw [spliced_molecule_Gamma G hp hL.ne' base roots z v]
  unfold splicedEnergyCenter splicedFrequency
  have ha : δ * L ^ (2 * γ) ≠ 0 := (mul_pos hδ (Real.rpow_pos_of_pos hL _)).ne'
  field_simp [ha]
  <;> ring

theorem spliced_energy_window {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (γ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (σ : GBranch G.tree → ℤ) (z : GenDecoration G d roots 0) (v : GBranch G.tree)
    (hbox : |splicedFrequency G D L γ δ base z.1 v - σ v| ≤ 1) :
    |G.molecule.Gamma L base (bondIndex G z.1) v - splicedEnergyCenter G hp D L γ δ base roots σ v| ≤
      δ⁻¹ * L ^ (-2 * γ) := by
  have ha : 0 < δ * L ^ (2 * γ) := mul_pos hδ (Real.rpow_pos_of_pos hL _)
  have hh : |G.molecule.Gamma L base (bondIndex G z.1) v - splicedEnergyCenter G hp D L γ δ base roots σ v| ≤
      1 / (δ * L ^ (2 * γ)) := by
    apply (le_div_iff₀ ha).mpr
    rw [← abs_of_pos ha, ← abs_mul, spliced_energy_residual G hp D hL hδ γ base roots σ z v, abs_sub_comm]
    exact hbox
  simpa only [one_div, mul_inv, ← Real.rpow_neg hL.le, neg_mul] using hh

end WaveTurbulence.LGSpine
