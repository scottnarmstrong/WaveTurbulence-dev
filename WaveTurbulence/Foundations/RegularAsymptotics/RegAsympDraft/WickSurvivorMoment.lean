/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSurvivorAmplitude

/-! # Surviving modulation moments cost no additional source frequency -/

public section
namespace WaveTurbulence.RegAsymp
open Finset

/-- Relabelling and removing links can only decrease the source first moment. -/
theorem sum_norm_wickSurvivor_le {d n : ℕ} (σ : Fin n → Fin 4) (β : Fin n → Mom d) :
    (∑ i : Fin (Fintype.card {j : Fin n // j ∉ wickTracedLinks σ}),
      ‖β ((wickSurvivorEquiv σ).symm i).val‖) ≤ ∑ j, ‖β j‖ := by
  classical
  rw [(wickSurvivorEquiv σ).symm.sum_comp (fun j => ‖β j.val‖)]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j : Fin n => σ j = 0) (fun j => ‖β j‖)]
  exact le_add_of_nonneg_right (sum_nonneg (fun _ _ => norm_nonneg _))

end WaveTurbulence.RegAsymp
