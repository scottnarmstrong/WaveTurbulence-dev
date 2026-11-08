/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.AsmG10
public import WaveTurbulence.Foundations.Flower.MkSlotsI.AsmG3
public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassId6
public import WaveTurbulence.Foundations.Flower.MkUnitsL.PrefixL

/-! # B3s-HELPER7 AsmG (7): `classRepGen_at` and **`classRepGen_prefix_of`**

* `selNativeBound : SelNativeBound` (`prod_selNative_le`, W:MkSlotsI/AsmG3.lean);
* **`classRepGen_at`**: `MkSlotsG.ClassRepGen 452` at the record `withC₁ (PB Pg C) (liftGen Pg.d)` from B3's gates at
  `Pg`, B3-2's V5W-2L class bound and the top decay at `PB Pg C`, the general slot obligation
  `GenSlotObligationAt Kg (PB Pg C)`, `η ≤ 1/4` and `Cgen Pg.d Pg.η Pg.C₁ Kg ≤ C` (`classRepGen_at_of` with the
  absorbed-selection bound and the proved class identity `classCentreIdentity`, W:MkSlotsI/ClassId6.lean);
* `genAsm_prefix_data`: B3-2's prefix data (gates, top decay, V5W-2L bound, `MkUnitsL.markedUnits_prefix_dataL` with
  `V5W2L.v5FrontierClassBoundL`) and the slot obligation at one constant `Kg` (`prefix_and`, `genSlotObligationAt_mono`);
* **`classRepGen_prefix_of (hslot : GenSlotObligation) : WTPrefix (MkSlotsG.ClassRepGen 452)`** (record
  `C₁ = liftGen d · max C₁ (Cgen d η C₁ Kg)`, `η ≤ min η₀ (1/4) ((g₁/2)²)`).

Adapted from α's `MkSlots.IntAsm.classRepAlphaJ_prefixL` (W:MkSlots/IntPrefix.lean) and B3-2's
`MkUnitsL.markedUnits_pieces_of_frontierL` (W:MkUnitsL/PrefixL.lean). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.MkSlotsI
open WaveTurbulence WaveTurbulence.LGSpine VineParamContract WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkUnits WaveTurbulence.VineA
open WaveTurbulence.Flower.MkSlots (withC₁)

/-- **The absorbed-selection bound holds** (`prod_selNative_le`). -/
theorem selNativeBound : SelNativeBound :=
  fun J pat t s kSel Rs mkF hsub a Mk hMk hRs hok => prod_selNative_le J pat t s kSel Rs mkF hsub a Mk hMk hRs hok

/-- **`ClassRepGen 452` at one parameter record** (the class identity is `classCentreIdentity`). -/
theorem classRepGen_at (Pg : WTParams) (C : ℝ) (E : GateEnv Pg)
    (hη : 0 < Pg.η) (hη4 : Pg.η ≤ 1 / 4) (hδ : 0 < Pg.δ) (hL2 : 2 ≤ Pg.L) (hC2 : 1 ≤ Pg.C₂) (hM9 : VINEPARAM)
    (Kg : ℕ → ℝ → ℝ) (hC : Cgen Pg.d Pg.η Pg.C₁ Kg ≤ C)
    (hV : V5W2L.V5FrontierClassBoundAtL (PB Pg C)) (htop : TopIncoherentDecayAtR (PB Pg C))
    (hslot : GenSlotObligationAt Kg (PB Pg C)) :
    MkSlotsG.ClassRepGen 452 (withC₁ (PB Pg C) (liftGen Pg.d)) :=
  classRepGen_at_of selNativeBound Pg C E hη hη4 hδ hL2 hC2 hM9 Kg hC hV htop hslot
    (classCentreIdentity Kg (PB Pg C))

/-- The prefix data of the general assembly: B3-2's gates, top decay and V5W-2L bound, and the slot obligation. -/
theorem genAsm_prefix_data (Kg : ℕ → ℝ → ℝ) (hslot : WTPrefix (GenSlotObligationAt Kg)) :
    WTPrefix (fun P => (((LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) ∧ V5W2L.V5FrontierClassBoundAtL P) ∧ GenSlotObligationAt Kg P) := by
  have hm1 : LargeConstantMonotone (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    leafwiseIncoherentDecay_largeConstantMonotone.and leafwiseCoherentApproximation30_largeConstantMonotone
  exact prefix_and (MkUnitsL.markedUnits_prefix_dataL V5W2L.v5FrontierClassBoundL) hslot
    ((hm1.and Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone).and
      MkUnitsL.v5FrontierClassBoundAtL_mono)
    (genSlotObligationAt_mono Kg)

/-- **The analytic core `ClassRepGen 452` on the prefix**, from the general slot obligation. -/
theorem classRepGen_prefix_of (hslot : GenSlotObligation) : WTPrefix (MkSlotsG.ClassRepGen 452) := by
  obtain ⟨Kg, -, hslotP⟩ := hslot
  have hall := genAsm_prefix_data Kg hslotP
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hall d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 < g1 := by
    rw [hg1]
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min η₀ (min (1 / 4) ((g1 / 2) ^ 2)), lt_min hη₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro η hηm φin hφin τ hτ φ hsol
  have hη0 : η ≤ η₀ := hηm.2.trans (min_le_left _ _)
  have hη4 : η ≤ 1 / 4 := hηm.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη2 : η ≤ 1 / 2 := by linarith
  have hη3 : η ≤ (g1 / 2) ^ 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁g, hC₁g, ν₀, hν₀, hrest⟩ := hη η ⟨hηm.1, hη0⟩ φin hφin τ hτ φ hsol
  set Cm : ℝ := max C₁g (Cgen d η C₁g Kg) with hCm
  have hlift := one_le_liftGen d
  have hCm1 : 1 ≤ Cm := hC₁g.trans (le_max_left _ _)
  refine ⟨liftGen d * Cm, ?_, ν₀, hν₀, ?_⟩
  · calc (1 : ℝ) ≤ Cm := hCm1
      _ ≤ liftGen d * Cm := le_mul_of_one_le_left (by linarith) hlift
  intro ν hν
  obtain ⟨δ₀, hδ₀, hrest2⟩ := hrest ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hrest3⟩ := hrest2 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨⟨⟨⟨hincP, hcohP⟩, htopP⟩, hVP⟩, hslotP'⟩ := hrest3 L hL
  let Pg : WTParams := ⟨d, γ, η, φin, τ, φ, C₁g, ν, δ, D, C₂, L⟩
  have hL2 : 2 ≤ L := hL₀.trans hL
  have E : GateEnv Pg :=
    { hd1 := by show 1 ≤ d; omega
      hL1 := by show 1 ≤ L; linarith
      hη0 := hηm.1.le
      hη := hη2
      hC1 := hC₁g
      hδ0 := hδ.1.le
      hκ := eta_pow_leN g1 η hg hηm.1 hη3 hη2
      hinc := hincP
      hcoh := hcohP }
  have hV' : V5W2L.V5FrontierClassBoundAtL (PB Pg Cm) :=
    MkUnitsL.v5FrontierClassBoundAtL_mono Pg Cm C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl hVP
  have htop' : TopIncoherentDecayAtR (PB Pg Cm) :=
    Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone Pg Cm C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl
      htopP
  have hslot' : GenSlotObligationAt Kg (PB Pg Cm) :=
    genSlotObligationAt_mono Kg Pg Cm C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl hslotP'
  exact classRepGen_at Pg Cm E hηm.1 hη4 hδ.1 hL2 hC₂ Vine.Param.vineparam Kg (le_max_right _ _) hV' htop' hslot'

end WaveTurbulence.Flower.MkSlotsI
