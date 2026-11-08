/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.Check
public import WaveTurbulence.Foundations.Flower.SelRes.Check

/-! # C5b COMP-MK: the D7 input discharged

D7-2 (finding F-C5b-1) proves the per-tree selected class sum `SelRes.selSumTargetT : FinalMKDefs.SelSumTargetT`.
With it, the per-component bound and the flower gate need only B4's marked Stage-1′ gate and D6b's regular bound:

* `markedComponentBoundAtI_18000_of`: `WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ) → RegularComponentTargetI →
  WTPrefixP (MarkedComponentBoundAtI 18000)`;
* **`flowerest1_of_B4_D6b`**: the same two inputs give `V2Chain.LayergardenFlowerV3Gate`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

open WaveTurbulence.Flower.ProtWhole

namespace WaveTurbulence.Flower.CompMK

/-- **The per-component bound at `B = 18000`** from B4's gate and D6b's regular bound (D7 discharged). -/
theorem markedComponentBoundAtI_18000_of {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500)
    (hcθ : 1 ≤ cθ) (hB4 : WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)) (hReg : RegularComponentTargetI) :
    WTPrefixP (MarkedComponentBoundAtI 18000) :=
  markedComponentBoundAtI_18000 hC₀ hcP hcP' hcθ hB4 SelRes.selSumTargetT hReg

/-- **The flower gate** from B4's gate and D6b's regular bound (D7 discharged). -/
theorem flowerest1_of_B4_D6b {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500)
    (hcθ : 1 ≤ cθ) (hB4 : WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)) (hReg : RegularComponentTargetI) :
    V2Chain.LayergardenFlowerV3Gate :=
  flowerest1_of_inputs hC₀ hcP hcP' hcθ hB4 SelRes.selSumTargetT hReg

example : SelSumTargetT := SelRes.selSumTargetT

-- B4's constant `cP = 452` (ruling R177)
example {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ) (hB4 : WTPrefix (Stage1ReductionAtMKFull C₀ 452 cθ))
    (hReg : RegularComponentTargetI) : V2Chain.LayergardenFlowerV3Gate :=
  flowerest1_of_B4_D6b hC₀ (by norm_num) (by norm_num) hcθ hB4 hReg

#print axioms markedComponentBoundAtI_18000_of
#print axioms flowerest1_of_B4_D6b

end WaveTurbulence.Flower.CompMK
