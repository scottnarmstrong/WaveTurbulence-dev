/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.SourceGapDyadics
/-! Actual selected small-gap pairs have all critical-atom dyadic scales simultaneously. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceAtomScaleExists` (sha256 0459d6efa939f629974c6043d53e24224b725600e010b49139692d1edb789df9) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}

/-- TARGET requirement (f), L2105: scales are chosen for the actual already selected
pairs. No gap lower bound or dyadic-coverage premise is added. -/
theorem exists_counting_atomScales {w d : ℕ} (G : Garden w)
    (C : CountingChoices γv G d) {L : ℝ} (hL : 0 < L) (γ η : ℝ)
    (hcap : 2 * L⁻¹ ≤ L ^ (-γ + η)) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ))
    (hsg : ∀ v, C.atomLabel v = .SG →
      SourceVine.HasChosenPair (C.first v) (C.second v) (fun x y =>
        Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG)) :
    ∃ scale : GBranch G.tree → ℝ, ∀ v, C.CriticalSG v →
      SourceVine.IsDyadicScale (scale v) ∧ L⁻¹ ≤ scale v ∧ scale v ≤ L ^ (-γ + η) ∧
        SourceVine.HasChosenPair (C.first v) (C.second v) (fun x y =>
          scale v / 2 ≤ ‖Molecule.gapAt L base κ x y‖ ∧
            ‖Molecule.gapAt L base κ x y‖ ≤ 2 * scale v) := by
  classical
  have hex (v : GBranch G.tree) : ∃ Q : ℝ, C.CriticalSG v →
      SourceVine.IsDyadicScale Q ∧ L⁻¹ ≤ Q ∧ Q ≤ L ^ (-γ + η) ∧
        SourceVine.HasChosenPair (C.first v) (C.second v) (fun x y =>
          Q / 2 ≤ ‖Molecule.gapAt L base κ x y‖ ∧ ‖Molecule.gapAt L base κ x y‖ ≤ 2 * Q) := by
    by_cases hv : C.CriticalSG v
    · obtain ⟨x, y, hx, hy, hgap⟩ := hsg v hv.1
      obtain ⟨Q, hdy, hlo, hhi, hcomp⟩ := exists_small_gap_scale hL γ η hcap base κ x y hgap
      exact ⟨Q, fun _ => ⟨hdy, hlo, hhi, x, y, hx, hy, hcomp⟩⟩
    · exact ⟨1, fun h => (hv h).elim⟩
  choose scale hscale using hex
  exact ⟨scale, hscale⟩

end WaveTurbulence.GammaLow.Famc
