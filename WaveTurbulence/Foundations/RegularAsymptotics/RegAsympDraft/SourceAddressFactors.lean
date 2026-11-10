/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceAddressPV

/-! # Extracting independent factors from actual source singular blocks -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Links Function

/-- A delta integral admits scalar extraction without an integrability
premise, by the defining Bochner integral convention. -/
theorem deltaInner_const_mul {d : ℕ} (c : ℂ) (H : Mom d → Mom d → ℂ) :
    NTSP.deltaInner (fun x y => c*H x y) = c*NTSP.deltaInner H := by
  simp only [NTSP.deltaInner,integral_const_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  ring

end WaveTurbulence.RegAsymp
