/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedEnergyWindows
public import WaveTurbulence.Foundations.Spine.SplicedAmplitudeSupport
/-! Nonzero summands in one frequency box satisfy the literal restricted-decoration predicate. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.Mole

theorem spliced_restricted_decoration {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (σ : GBranch G.tree → ℤ) (z : GenDecoration G d roots 0)
    (hz : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0)
    (hbox : ∀ v, |splicedFrequency G D L γ δ base z.1 v - σ v| ≤ 1) :
    G.molecule.IsRestricted L γ δ base (splicedEnergyCenter G hp D L γ δ base roots σ)
      D.center (bondIndex G z.1) := by
  have hdec := spliced_molecule_decoration G hp hL.ne' base roots z
  have hballs := (splicedMomentumAmplitude_support G D hD L γ η base z.1 hz).2.2
  constructor
  · intro v _
    exact spliced_energy_window G hp D hL hδ γ base roots σ z v (hbox v)
  · intro x
    by_cases hx : G.molecule.out x = true
    · have hm : x ∈ G.molecule.bonds := by simp only [Molecule.bonds, mem_filter, Finset.mem_univ, true_and]; exact hx
      exact hballs x hm
    · have hx' : G.molecule.out x = false := Bool.eq_false_iff.mpr hx
      have hm : G.molecule.mate x ∈ G.molecule.bonds := by
        simp only [Molecule.bonds, mem_filter, Finset.mem_univ, true_and, G.molecule.out_mate, hx', Bool.not_false]
      have hh := hballs (G.molecule.mate x) hm
      simpa only [Molecule.kvec, hdec.1 x, hD.1 x] using hh

theorem spliced_restricted_of_floor {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (σ : GBranch G.tree → ℤ) (z : GenDecoration G d roots 0)
    (hz : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0)
    (hσ : ∀ v, ⌊splicedFrequency G D L γ δ base z.1 v⌋ = σ v) :
    G.molecule.IsRestricted L γ δ base (splicedEnergyCenter G hp D L γ δ base roots σ)
      D.center (bondIndex G z.1) := by
  apply spliced_restricted_decoration G hp D hD hL hδ γ η base roots σ z hz
  intro v
  rw [← hσ v, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
  linarith [Int.lt_floor_add_one (splicedFrequency G D L γ δ base z.1 v)]

end WaveTurbulence.LGSpine
