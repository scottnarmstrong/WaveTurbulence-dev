/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.Top

/-! # C5b COMP-MK: exports, exact-type examples and axioms

* `nonreg_of_marked`: `NonregComponentBoundAtI` is `MarkedComponentBoundAtI` on a sub-carrier (text alignment). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

open WaveTurbulence.Flower.ProtWhole

namespace WaveTurbulence.Flower.CompMK

/-- Text alignment: the non-regular statement is the per-component statement on a smaller carrier. -/
theorem nonreg_of_marked {B : ℝ} {Pm : ℕ} {P : WTParams} (h : MarkedComponentBoundAtI B Pm P) :
    NonregComponentBoundAtI B Pm P := by
  intro hγ p hp R hR1 hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel A hA hplain hTC
  exact h hγ p hp R hR1 hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel A
    (fun LG hLG => ⟨(hA LG hLG).1, (hA LG hLG).2.1, (hA LG hLG).2.2.1, (hA LG hLG).2.2.2.1, (hA LG hLG).2.2.2.2.1⟩)
    hplain hTC

/-! ## Exact-type examples (brief items 1–3). -/

-- item 1: the non-regular part of `MarkedComponentBoundAtI 18000` (at 17999), from B4 and D7
example {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500) (hcθ : 1 ≤ cθ)
    (hB4 : WTPrefix (Stage1ReductionAtMKSel C₀ cP cθ)) (hD7 : SelSumTargetT) :
    WTPrefixP (NonregComponentBoundAtI 17999) :=
  nonregPrefix hC₀ hcP hcP' hcθ hB4 hD7

-- item 1 at B4's constant `cP = 452` (ruling R177)
example {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hB4 : WTPrefix (Stage1ReductionAtMKSel C₀ 452 cθ)) (hD7 : SelSumTargetT) :
    WTPrefixP (NonregComponentBoundAtI 17999) :=
  nonregPrefix hC₀ (by norm_num) (by norm_num) hcθ hB4 hD7

-- item 2: the glue
example (hNR : WTPrefixP (NonregComponentBoundAtI 17999)) (hReg : WTPrefixP (RegularComponentBoundAtI 17999)) :
    WTPrefixP (MarkedComponentBoundAtI 18000) :=
  markedComponentBoundAtI_of hNR hReg

-- B4's Full gate (ruling R177, world `MkDefs/Stage1MKFull.lean`) gives the consumed gate
example {C₀ : ℕ} {cP cθ : ℝ} {P : WTParams} (h : Stage1ReductionAtMKFull C₀ cP cθ P) :
    Stage1ReductionAtMKSel C₀ cP cθ P :=
  stage1ReductionAtMKSel_of_full h

-- the per-component bound at `B = 18000` (ruling R175) from the three inputs
example {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500) (hcθ : 1 ≤ cθ)
    (hB4 : WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)) (hD7 : SelSumTargetT) (hReg : RegularComponentTargetI) :
    WTPrefixP (MarkedComponentBoundAtI 18000) :=
  markedComponentBoundAtI_18000 hC₀ hcP hcP' hcθ hB4 hD7 hReg

-- item 3: the composite, through CAPS-STABLE's consumer (B4's `cP = 452`)
example {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cθ : ℝ} (hcθ : 1 ≤ cθ)
    (hB4 : WTPrefix (Stage1ReductionAtMKFull C₀ 452 cθ)) (hD7 : SelSumTargetT) (hReg : RegularComponentTargetI) :
    V2Chain.LayergardenFlowerV3Gate :=
  flowerest1_of_inputs hC₀ (by norm_num) (by norm_num) hcθ hB4 hD7 hReg

-- the consumer's exact statement
example (B : ℝ) (hB0 : 0 ≤ B) (hB : B ≤ 24000) (hM : WTPrefixP (MarkedComponentBoundAtI B)) :
    V2Chain.LayergardenFlowerV3Gate :=
  CapsStable.flower_v3_of_marked B hB0 hB hM

#print axioms summable_kgTerm_capWt_gen
#print axioms kernelKgen_eq_sum_sel
#print axioms sum_compValue_eq_sum_pieces
#print axioms card_protI_le
#print axioms stage1Counts_restrict
#print axioms sum_eq_sum_powerset
#print axioms selMass_mul_prod
#print axioms markedExtra_le
#print axioms bracket_le
#print axioms budget_le
#print axioms budget_17999
#print axioms nonreg_at
#print axioms markedTwistClosed_filter_nonreg
#print axioms marked_at
#print axioms prefixP_and_indep
#print axioms markedComponentBoundAtI_of
#print axioms coarseSplicedAtMK_largeConstantMonotone
#print axioms fineSplicedHalfMK_largeConstantMonotone
#print axioms ladderFourierAtMKFace_largeConstantMonotone
#print axioms stage1ReductionAtMKSel_largeConstantMonotone
#print axioms nonregPrefix
#print axioms markedComponentBoundAtI_18000
#print axioms flowerest1_of_inputs
#print axioms stage1ReductionAtMKSel_of_full
#print axioms nonreg_of_marked

end WaveTurbulence.Flower.CompMK
