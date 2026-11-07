/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineDouble6
/-! The label count of a VC formed by two double bonds, part 7: the count input `𝔉` (DH23 L1801, last sentence). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace DoubleShape
variable {M : Molecule V D} {K : VineCut M} (S : DoubleShape K)
include S

/-- **The count `𝔉` of a VC formed by two double bonds** (DH23 L1801, last sentence): fix `(κx₁, gap)`
(`L^d (ρL)^d` choices), then Lemma `basiccount` (1) for the remaining vector (energy strip at the middle atom). -/
theorem labelSet_le_vineG {L γ δ : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop} (hd : 1 ≤ d) (hL : 1 ≤ L)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (R ρ : ℝ) (hR : 0 < R) (hρ0 : 0 ≤ ρ) (hρL : 1 ≤ ρ * L)
    (hgapLow : ∀ κ', Adm κ' → R / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖)
    (hball : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' K.x₁ K.x₂ - r₀‖ ≤ ρ) :
    ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (K.labelSet L γ δ w Adm c β k0).encard ≤
        ENNReal.ofReal (vineG d L γ δ R ρ (9 ^ d * 5 ^ d * (2 * d)) 0) := by
  intro c β k0 hP
  have hL0 : 0 < L := by linarith
  obtain ⟨r₀, hr₀⟩ := hball c β k0 hP
  have h1 := S.labelSet_encard_le hP hL0 R ρ r₀ hgapLow hr₀
  have hτ : 0 ≤ δ⁻¹ * L ^ (-2 * γ) / 2 := by positivity
  have h2 := tripleFin_card_le (show 0 < d by omega) hL0 hτ hR hρ0 (k0 K.x₁ - w) r₀ (k0 K.x₁ - k0 K.y₁)
    (βx := β S.x)
  have h3 := double_real d (γ := γ) hd hL hδ hδ1 hR hρ0 hρL
  refine (ENat.toENNReal_le.2 h1).trans ?_
  rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (h2.trans h3)

end DoubleShape
end WaveTurbulence.FinalCount
