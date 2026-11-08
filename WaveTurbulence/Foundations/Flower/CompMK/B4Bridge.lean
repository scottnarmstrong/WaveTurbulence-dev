/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.D7Bridge
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.ZeroFinal

/-! # C5b COMP-MK: B4's gate plugged in — the flower gate from B3s and D6b

B4 (READY) proves `Stage1MKGate.stage1ReductionAtMKFull_of_B3s : WTPrefix (MarkedClassRepresentsMK cP cθ) →
∃ C₀ ≥ 2, WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)` (with its `b2eIX` and `zeroVanish_prefix` inside). With D7
discharged (`D7Bridge`), the per-component bound and the flower gate rest on exactly two inputs:
B3s's `WTPrefix (MarkedClassRepresentsMK cP cθ)` and D6b's `RegularComponentTargetI`.

* `flowerest1_of_gate`: from `∃ C₀ ≥ 1, WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)` and D6b;
* **`flowerest1_of_B3s_D6b`** (and `markedComponentBoundAtI_18000_of_B3s_D6b`): from B3s and D6b, any
  `0 ≤ cP ≤ 500`, `1 ≤ cθ`; at B4's `cP = 452`: `flowerest1_of_B3s_D6b_452`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.ProtWhole
open WaveTurbulence.Flower.Stage1MKGate

namespace WaveTurbulence.Flower.CompMK

/-- The flower gate from B4's gate (existential class-count constant) and D6b's regular bound. -/
theorem flowerest1_of_gate {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500) (hcθ : 1 ≤ cθ)
    (hB4 : ∃ C₀ : ℕ, 1 ≤ C₀ ∧ WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)) (hReg : RegularComponentTargetI) :
    V2Chain.LayergardenFlowerV3Gate := by
  obtain ⟨C₀, hC₀, hG⟩ := hB4
  exact flowerest1_of_B4_D6b hC₀ hcP hcP' hcθ hG hReg

/-- **The per-component bound at `B = 18000`** from B3s's class representation and D6b's regular bound. -/
theorem markedComponentBoundAtI_18000_of_B3s_D6b {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500) (hcθ : 1 ≤ cθ)
    (hB : WTPrefix (MarkedClassRepresentsMK cP cθ)) (hReg : RegularComponentTargetI) :
    WTPrefixP (MarkedComponentBoundAtI 18000) := by
  obtain ⟨C₀, hC₀, hG⟩ := stage1ReductionAtMKFull_of_B3s cP cθ hB
  exact markedComponentBoundAtI_18000_of (by omega) hcP hcP' hcθ hG hReg

/-- **The flower gate from B3s's class representation and D6b's regular bound** (B4, D7 discharged). -/
theorem flowerest1_of_B3s_D6b {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500) (hcθ : 1 ≤ cθ)
    (hB : WTPrefix (MarkedClassRepresentsMK cP cθ)) (hReg : RegularComponentTargetI) :
    V2Chain.LayergardenFlowerV3Gate := by
  obtain ⟨C₀, hC₀, hG⟩ := stage1ReductionAtMKFull_of_B3s cP cθ hB
  exact flowerest1_of_gate hcP hcP' hcθ ⟨C₀, by omega, hG⟩ hReg

/-- At B4's protected-loss constant `cP = 452` (R175/R177). -/
theorem flowerest1_of_B3s_D6b_452 {cθ : ℝ} (hcθ : 1 ≤ cθ) (hB : WTPrefix (MarkedClassRepresentsMK 452 cθ))
    (hReg : RegularComponentTargetI) : V2Chain.LayergardenFlowerV3Gate :=
  flowerest1_of_B3s_D6b (by norm_num) (by norm_num) hcθ hB hReg

-- exact-type examples (the two remaining inputs)
example {cθ : ℝ} (hcθ : 1 ≤ cθ) (hB : WTPrefix (Stage1MKGate.MarkedClassRepresentsMK 452 cθ))
    (hReg : ProtWhole.RegularComponentTargetI) : V2Chain.LayergardenFlowerV3Gate :=
  flowerest1_of_B3s_D6b_452 hcθ hB hReg

example {cθ : ℝ} (hcθ : 1 ≤ cθ) (hB : WTPrefix (Stage1MKGate.MarkedClassRepresentsMK 452 cθ))
    (hReg : ProtWhole.RegularComponentTargetI) : WTPrefixP (MkDefs.MarkedComponentBoundAtI 18000) :=
  markedComponentBoundAtI_18000_of_B3s_D6b (by norm_num) (by norm_num) hcθ hB hReg

#print axioms flowerest1_of_gate
#print axioms markedComponentBoundAtI_18000_of_B3s_D6b
#print axioms flowerest1_of_B3s_D6b
#print axioms flowerest1_of_B3s_D6b_452

end WaveTurbulence.Flower.CompMK
