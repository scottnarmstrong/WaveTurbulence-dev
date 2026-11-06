/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.MolPres
public import WaveTurbulence.Foundations.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
import Mathlib.Tactic
/-! Facts about decorations in the frequency spectrum: dart momenta near the centers, the formula
`α_v = δ L^{2γ}(-Γ_v + g_v) + ξ_v`, conservation at saturated atoms. -/
@[expose] public section
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine

variable {w d : ℕ} (G : Garden w)

theorem dart_near_center (D : SplicedKernelData G d) (hamp : SplicedAmplitudeBounds G D)
    (L : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) (hκ : ∀ x, κ (G.molecule.mate x) = κ x)
    (hb : ∀ x ∈ G.molecule.bonds, ‖base + latticePoint L (κ x) - D.center x‖ ≤ 1) (x : GardenDart G) :
    ‖Molecule.kvec L base κ x - D.center x‖ ≤ 1 := by
  by_cases hx : G.molecule.out x = true
  · have : x ∈ G.molecule.bonds := by simp [Molecule.bonds, hx]
    exact hb x this
  · have hm : G.molecule.mate x ∈ G.molecule.bonds := by
      simp [Molecule.bonds, G.molecule.out_mate, hx]
    have := hb _ hm
    rw [hκ x, hamp.1 x] at this
    exact this

theorem splicedFrequency_eq (hp : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (D : SplicedKernelData G d) (γ δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) (v : GBranch G.tree) :
    splicedFrequency G D L γ δ base z.1 v =
      δ * L ^ (2 * γ) * (- G.molecule.Gamma L base (bondIndex G z.1) v +
        Mole.gardenSource G hp (fun i => ‖base + latticePoint L (roots i)‖ ^ 2) v) + D.frequency v := by
  have h := spliced_molecule_Gamma G hp hL base roots z v
  unfold splicedFrequency
  have : (((G.sign v.toNode : ℤˣ) : ℤ) : ℝ) * omegaNode G (cosetDecoration G L base z.1) v =
      - G.molecule.Gamma L base (bondIndex G z.1) v +
        Mole.gardenSource G hp (fun i => ‖base + latticePoint L (roots i)‖ ^ 2) v := by
    linarith
  calc (((G.sign v.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) * omegaNode G (cosetDecoration G L base z.1) v
          + D.frequency v
      = δ * L ^ (2 * γ) * ((((G.sign v.toNode : ℤˣ) : ℤ) : ℝ) *
          omegaNode G (cosetDecoration G L base z.1) v) + D.frequency v := by ring
    _ = _ := by rw [this]

theorem conservation_deg_four (hp : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) (a : GBranch G.tree)
    (hdeg : G.molecule.deg a = 4) :
    ∑ x ∈ G.molecule.dartsAt a, G.molecule.dartSign x • Molecule.kvec L base (bondIndex G z.1) x = 0 := by
  have hdec := spliced_molecule_decoration G hp hL base roots z
  have h := hdec.2 a (Finset.mem_univ a)
  rw [h]
  exact gardenSource_eq_zero_of_deg_four G hp _ a hdeg

end WaveTurbulence.Ladder
