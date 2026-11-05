/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickAmplitudeFactor
public import WaveTurbulence.Foundations.RegAsymp.SurvivingProfile

/-! # The surviving Wick amplitude is the original NT half-cell amplitude -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Finset

/-- The same enumeration used for the surviving coefficient, with the
source pattern's equivalent untraced predicate. -/
def wickSurvivorEquiv {n : ℕ} (σ : Fin n → Fin 4) :
    {j : Fin n // σ j = 0} ≃ Fin (Fintype.card {j : Fin n // j ∉ wickTracedLinks σ}) :=
  (Equiv.subtypeEquivRight (fun j => by simp [wickTracedLinks])).trans
    (survivingEnergyEquiv (wickTracedLinks σ))

/-- No new amplitude estimate is required: after literal enumeration,
the untouched factors are exactly halfCellAmplitude in the smaller order. -/
theorem wickSurvivorAmplitude_eq_halfCellAmplitude {d n : ℕ}
    (L : ℝ) (σ : Fin n → Fin 4) (z : (Fin n × Fin 2) → Fin d → ℤ)
    (β γ : Fin n → Mom d) (u : {j : Fin n // σ j = 0} → (Fin d → ℤ) × (Fin d → ℤ)) :
    (∏ j, wickLinkAmplitude L z β γ j.val (u j)) =
      halfCellAmplitude (fun p => z (((wickSurvivorEquiv σ).symm p.1).val,p.2))
        (fun i => β ((wickSurvivorEquiv σ).symm i).val)
        (fun i => γ ((wickSurvivorEquiv σ).symm i).val)
        (fun i => latticePoint L (u ((wickSurvivorEquiv σ).symm i)).1)
        (fun i => latticePoint L (u ((wickSurvivorEquiv σ).symm i)).2) := by
  rw [halfCellAmplitude_eq_prod_wickLinkAmplitude]
  exact ((wickSurvivorEquiv σ).symm.prod_comp
    (fun j => wickLinkAmplitude L z β γ j.val (u j))).symm

end WaveTurbulence.RegAsymp
