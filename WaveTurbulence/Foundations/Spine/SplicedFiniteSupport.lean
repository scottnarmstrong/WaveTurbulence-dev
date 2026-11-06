/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.FiniteCosetBall
public import WaveTurbulence.Foundations.Spine.SplicedAmplitudeSupport
public import WaveTurbulence.Foundations.Spine.SplicedSelectedKernel
public import Mathlib.Data.Fintype.Pi
/-! The actual compactly supported spliced decoration sums have finite support. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset

theorem finite_bounded_garden_decorations {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    {L : ℝ} (hL : 0 < L) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (center : GardenDart G → Mom d) :
    {z : GenDecoration G d roots 0 | ∀ x, ‖base + latticePoint L (bondIndex G z.1 x) - center x‖ ≤ 1}.Finite := by
  have hfin := Set.Finite.pi' (fun x : GardenDart G => finite_coset_unit_ball hL base (center x))
  exact Set.Finite.preimage (bondIndex_injective G hp roots).injOn hfin

 theorem finite_spliced_amplitude_support {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    {L : ℝ} (hL : 0 < L) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    {z : GenDecoration G d roots 0 | splicedMomentumAmplitude G D L γ η base z.1 ≠ 0}.Finite := by
  apply (finite_bounded_garden_decorations G hp hL base roots D.center).subset
  intro z hz x
  have hballs := (splicedMomentumAmplitude_support G D hD L γ η base z.1 hz).2.2
  have hdec := spliced_molecule_decoration G hp hL.ne' base roots z
  by_cases hx : G.molecule.out x = true
  · exact hballs x (by simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]; exact hx)
  · have hx' : G.molecule.out x = false := Bool.eq_false_iff.mpr hx
    have hm : G.molecule.mate x ∈ G.molecule.bonds := by
      simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and, G.molecule.out_mate, hx', Bool.not_false]
    have hh := hballs (G.molecule.mate x) hm
    simpa only [hdec.1 x, hD.1 x] using hh

 theorem finite_splicedSelectedCarrier {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (C : SourceVine.CountingChoices G d)
    {L : ℝ} (hL : 0 < L) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    (splicedSelectedCarrier G D C L γ η base roots).Finite :=
  (finite_spliced_amplitude_support G hp D hD hL γ η base roots).subset (fun _ h => h.1)

end WaveTurbulence.LGSpine
