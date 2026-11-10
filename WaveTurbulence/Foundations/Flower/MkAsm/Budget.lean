/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.Fam.Top

/-! # A5 MK-ASM: the loss constant `BcMK`, the two component-to-core statements, and the final consumer.

Copied by source from the S-MARKED probe (sections 1 and the end; see COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkAsm

/-- The core loss per `Pm` used by the marked route. -/
noncomputable def BcMK (d : ℕ) : ℝ := 100000 * d

theorem BcMK_hBc : ∀ d : ℕ, 3 ≤ d → BcMK d + 80 * d + 3 < (100 * (d : ℝ)) ^ 3 := by
  intro d hd
  have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h9 : (9 : ℝ) * d ≤ (d : ℝ) ^ 3 := by nlinarith [sq_nonneg ((d : ℝ) - 3)]
  have e : (100 * (d : ℝ)) ^ 3 = 1000000 * (d : ℝ) ^ 3 := by ring
  unfold BcMK
  rw [e]
  nlinarith

/-- **MK-ASM export F**: Core-F from the per-component marked bound (`MarkedComponentBoundAtI`, at the concrete
marking rule `protSkOf`; B0 finding F-B0-1). -/
def CoreFOfComponents : Prop :=
  ∀ B : ℝ, 0 ≤ B → B ≤ 24000 → WTPrefixP (MarkedComponentBoundAtI B) →
    WTPrefixP (Fam.FlowerCoreFiltAt BcMK)

/-- **MK-ASM export G**: Core-G from the per-component marked bound. -/
def CoreGOfComponents : Prop :=
  ∀ B : ℝ, 0 ≤ B → B ≤ 24000 → WTPrefixP (MarkedComponentBoundAtI B) →
    WTPrefixP (Fam.FlowerCoreGainAt BcMK)

/-- The final consumer, as on main (`layergardenFlower_v3_of_cores`), at `BcMK`. -/
theorem flower_v3_of_marked (hF : CoreFOfComponents)
    (hG : CoreGOfComponents) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : B ≤ 24000) (hM : WTPrefixP (MarkedComponentBoundAtI B)) :
    V2Chain.LayergardenFlowerV3Gate :=
  Fam.layergardenFlower_v3_of_cores BcMK BcMK_hBc (hF B hB0 hB hM) (hG B hB0 hB hM)

end WaveTurbulence.Flower.MkAsm
