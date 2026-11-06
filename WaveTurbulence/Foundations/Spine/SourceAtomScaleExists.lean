/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.SourceGapDyadics
/-! Actual selected small-gap pairs admit all critical-atom dyadic scales simultaneously. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

/-- TARGET requirement (f), L2105: scales are chosen for the actual already selected
pairs. No gap lower bound or dyadic-coverage premise is added. -/
theorem exists_counting_atomScales {w d : ℕ} (G : Garden w)
    (C : SourceVine.CountingChoices G d) {L : ℝ} (hL : 0 < L) (γ η : ℝ)
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

end WaveTurbulence.LGSpine
