/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.Prefix
public import WaveTurbulence.Foundations.Flower.CompMK.Glue
public import WaveTurbulence.Foundations.Flower.CapsStable.Top
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MKFull

/-! # C5b COMP-MK: the per-component bound at `B = 18000` and the flower gate from the three inputs

* `stage1ReductionAtMKSel_of_full`: B4's `MkDefs.Stage1ReductionAtMKFull` (rulings R177, R180) gives this area's
  `Stage1ReductionAtMKSel` (drop the output `(selR π).card ≤ nProt`; `selMassMK` is `selMass`).
* `markedComponentBoundAtI_18000`: B4's gate, D7's selected class sum and D6b's regular bound give
  `WTPrefixP (MarkedComponentBoundAtI 18000)` (ruling R175).
* **`flowerest1_of_inputs`**: the same inputs give `V2Chain.LayergardenFlowerV3Gate`, through CAPS-STABLE's
  `flower_v3_of_marked` (`0 ≤ 18000 ≤ 24000`). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

open WaveTurbulence.Flower.ProtWhole

namespace WaveTurbulence.Flower.CompMK

/-- **B4's Full gate gives the gate this area consumes.** -/
theorem stage1ReductionAtMKSel_of_full {C₀ : ℕ} {cP cθ : ℝ} {P : WTParams}
    (h : Stage1ReductionAtMKFull C₀ cP cθ P) : Stage1ReductionAtMKSel C₀ cP cθ P := by
  intro p hp R hR hRmax N hN1 hN J hJ pat kSel t ht s hs A hA hplain hTC roots hh b Rf σ Rs dag hb hhb hRf hRs
    hhigh
  obtain ⟨S, Cl, hCl, cls, members, sel, selR, hpart, hpc, hsound, hord, hcnt⟩ :=
    h p hp R hR hRmax N hN1 hN J hJ pat kSel t ht s hs A hA hplain hTC roots hh b Rf σ Rs dag hb hhb hRf hRs hhigh
  exact ⟨S, Cl, hCl, cls, members, sel, selR, hpart,
    fun π => ⟨(hpc π).1, (hpc π).2.1, (hpc π).2.2.1, (hpc π).2.2.2.1, (hpc π).2.2.2.2.1, (hpc π).2.2.2.2.2.1⟩,
    hsound, hord, hcnt⟩

theorem wtPrefix_sel_of_full {C₀ : ℕ} {cP cθ : ℝ} (h : WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)) :
    WTPrefix (Stage1ReductionAtMKSel C₀ cP cθ) :=
  FinalMKPin.wtPrefix_mono h fun _ => stage1ReductionAtMKSel_of_full

/-- **The per-component bound at `B = 18000`** from the three inputs:
* `hB4`: B4's marked Stage-1′ gate `Stage1ReductionAtMKFull` (ruling R177), with class-count constant `C₀ ≥ 1`,
  protected loss `0 ≤ cP ≤ 500` (B4: `cP = 452`) and filter constant `cθ ≥ 1`;
* `hD7`: D7's selected class sum with per-tree scales under the marked gates (`SelSumTargetT`, finding F-C5b-1);
* `hReg`: D6b's `RegularComponentTargetI` (used at `B = 17999 ≥ 74`). -/
theorem markedComponentBoundAtI_18000 {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500)
    (hcθ : 1 ≤ cθ) (hB4 : WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)) (hD7 : SelSumTargetT)
    (hReg : RegularComponentTargetI) : WTPrefixP (MarkedComponentBoundAtI 18000) :=
  markedComponentBoundAtI_of (nonregPrefix hC₀ hcP hcP' hcθ (wtPrefix_sel_of_full hB4) hD7) (hReg 17999 (by norm_num))

/-- **The flower gate from the three inputs** (brief item 3). -/
theorem flowerest1_of_inputs {C₀ : ℕ} (hC₀ : 1 ≤ C₀) {cP cθ : ℝ} (hcP : 0 ≤ cP) (hcP' : cP ≤ 500)
    (hcθ : 1 ≤ cθ) (hB4 : WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ)) (hD7 : SelSumTargetT)
    (hReg : RegularComponentTargetI) : V2Chain.LayergardenFlowerV3Gate :=
  CapsStable.flower_v3_of_marked 18000 (by norm_num) (by norm_num)
    (markedComponentBoundAtI_18000 hC₀ hcP hcP' hcθ hB4 hD7 hReg)

end WaveTurbulence.Flower.CompMK
