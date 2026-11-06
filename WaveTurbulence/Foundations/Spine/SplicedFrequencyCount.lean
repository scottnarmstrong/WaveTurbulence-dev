/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SplicedRestrictedDecoration
public import WaveTurbulence.Foundations.Spine.SourceFinalCountInputs
/-! Count each actual garden frequency fiber by the literal maximized molecular countE. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set WaveTurbulence.Mole

/-- Actual nonzero summands with all fixed source choices in a single integer frequency box. -/
def splicedFrequencyFiber {w d : ℕ} (G : Garden w) (D : SplicedKernelData G d)
    (C : SourceVine.CountingChoices G d) (L γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (σ : GBranch G.tree → ℤ) : Set (GenDecoration G d roots 0) :=
  {z | splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 ∧
    C.Admissible L γ η base (bondIndex G z.1) ∧
    ∀ v, ⌊splicedFrequency G D L γ δ base z.1 v⌋ = σ v}

theorem encard_splicedFrequencyFiber_le_countE {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (C : SourceVine.CountingChoices G d) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (σ : GBranch G.tree → ℤ) :
    (splicedFrequencyFiber G D C L γ η δ base roots σ).encard ≤
      G.molecule.countE L γ δ base (splicedCountingAdmissible G D C L γ η base roots) := by
  let c := gardenSource G hp (fun i => base + latticePoint L (roots i))
  let β := splicedEnergyCenter G hp D L γ δ base roots σ
  let Adm := splicedCountingAdmissible G D C L γ η base roots
  let T : Set (GardenDart G → (Fin d → ℤ)) := {κ |
    G.molecule.IsDecoration L base c κ ∧ G.molecule.IsRestricted L γ δ base β D.center κ ∧ Adm κ}
  have hmap : Set.MapsTo (fun z : GenDecoration G d roots 0 => bondIndex G z.1)
      (splicedFrequencyFiber G D C L γ η δ base roots σ) T := by
    intro z hz
    rcases hz with ⟨hamp, hC, hσ⟩
    have hs := splicedMomentumAmplitude_support G D hD L γ η base z.1 hamp
    exact ⟨spliced_molecule_decoration G hp hL.ne' base roots z,
      spliced_restricted_of_floor G hp D hD hL hδ γ η base roots σ z hamp hσ,
      ⟨z, (fun _ => rfl), hs.1, hs.2.1⟩, hC⟩
  have hcard : (splicedFrequencyFiber G D C L γ η δ base roots σ).encard ≤ T.encard :=
    Set.encard_le_encard_of_injOn hmap (bondIndex_injective G hp roots).injOn
  apply hcard.trans
  have hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0 := by
    intro v _ hdeg
    exact gardenSource_eq_zero_of_deg_four G hp _ v hdeg
  unfold Molecule.countE
  exact le_iSup_of_le c (le_iSup_of_le hc (le_iSup_of_le β (le_iSup_of_le D.center
    (le_iSup_of_le hD.1 le_rfl))))

end WaveTurbulence.LGSpine
