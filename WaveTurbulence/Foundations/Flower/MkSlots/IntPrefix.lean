/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm4
public import WaveTurbulence.Foundations.Flower.MkUnits.Prefix

/-! # B3s MK-SLOTS (integration, prefix): milestone α with `|J| = R` on the prefix

* `alpha_prefix_data`: B3's prefix data (gates, top decay, V5W's weighted class bound) and the cap-slot obligation
  at one constant `Kc`;
* `classRepAlphaJ_prefixL`: `1 ≤ L ∧ ClassRepAlphaJ cP` on the prefix, for `37 ≤ cP`, given `CapSlotObligation`
  (at the record `withC₁ (PB Pg Cm) (c_F^{16})`, `Cm = max C₁ (CalphaJ d η C₁ Kc)`, through `classRepAlphaJ_at`);
* **`classRepAlphaJ_prefix`**, **`markedClassRepresentsMKαJ_prefix`** (the latter through
  `markedClassRepresentsMKαJ_of_rep`).

Adapted from `MkUnits/Prefix.lean` (`markedUnits_pieces_of_frontier`, see `COPIED-SHA256SUMS`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.MkSlots.IntAsm
open WaveTurbulence WaveTurbulence.LGSpine VineParamContract WaveTurbulence.Represents
  WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Flower.Stage1WVine
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkUnits WaveTurbulence.VineA
/-- The prefix data of the α assembly: B3's gates, top decay and V5W bound, and the cap-slot obligation. -/
theorem alpha_prefix_data (Kc : ℕ → ℝ → ℝ) (hcap : WTPrefix (CapSlotObligationAt Kc)) :
    WTPrefix (fun P => (((LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) ∧ V5FrontierClassBoundAt P) ∧ CapSlotObligationAt Kc P) := by
  have hm1 : LargeConstantMonotone (fun P => LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) :=
    leafwiseIncoherentDecay_largeConstantMonotone.and leafwiseCoherentApproximation30_largeConstantMonotone
  exact prefix_and (markedUnits_prefix_data V5WT.v5FrontierClassBound) hcap
    ((hm1.and Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone).and v5FrontierClassBoundAt_mono)
    (capSlotObligationAt_mono Kc)

/-- **`ClassRepAlphaJ` on the prefix** (with `1 ≤ L`). -/
theorem classRepAlphaJ_prefixL (cP : ℝ) (hcP : 37 ≤ cP) (hcap : CapSlotObligation) :
    WTPrefix (fun P => 1 ≤ P.L ∧ ClassRepAlphaJ cP P) := by
  obtain ⟨Kc, -, hcapP⟩ := hcap
  have hall := alpha_prefix_data Kc hcapP
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hall d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 < g1 := by
    rw [hg1]
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min η₀ (min (1 / 2) ((g1 / 2) ^ 2)), lt_min hη₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro η hηm φin hφin τ hτ φ hsol
  have hη0 : η ≤ η₀ := hηm.2.trans (min_le_left _ _)
  have hη2 : η ≤ 1 / 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη3 : η ≤ (g1 / 2) ^ 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁g, hC₁g, ν₀, hν₀, hrest⟩ := hη η ⟨hηm.1, hη0⟩ φin hφin τ hτ φ hsol
  set Cm : ℝ := max C₁g (CalphaJ d η C₁g Kc) with hCm
  have hcF : 1 ≤ frontierConst d ^ 16 := one_le_pow₀ (one_le_frontierConst d)
  have hCm1 : 1 ≤ Cm := hC₁g.trans (le_max_left _ _)
  refine ⟨frontierConst d ^ 16 * Cm, ?_, ν₀, hν₀, ?_⟩
  · calc (1 : ℝ) ≤ Cm := hCm1
      _ ≤ frontierConst d ^ 16 * Cm := le_mul_of_one_le_left (by linarith) hcF
  intro ν hν
  obtain ⟨δ₀, hδ₀, hrest2⟩ := hrest ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hrest3⟩ := hrest2 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨⟨⟨⟨hincP, hcohP⟩, htopP⟩, hVP⟩, hcapP'⟩ := hrest3 L hL
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
  have hV' : V5FrontierClassBoundAt (PB Pg Cm) :=
    v5FrontierClassBoundAt_mono Pg Cm C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl hVP
  have htop' : TopIncoherentDecayAtR (PB Pg Cm) :=
    Stage1WNoVine.topIncoherentDecayAtR_largeConstantMonotone Pg Cm C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl htopP
  have hcap' : CapSlotObligationAt Kc (PB Pg Cm) :=
    capSlotObligationAt_mono Kc Pg Cm C₂ hC₁g hC₂ hδ.1 hL2 (le_max_left _ _) le_rfl hcapP'
  refine ⟨show (1 : ℝ) ≤ L by linarith, ?_⟩
  exact classRepAlphaJ_at Pg Cm E htopP hηm.1 hδ.1 hL2 hC₂ Vine.Param.vineparam Kc (le_max_right _ _) hV' htop' hcap'
    cP hcP

end WaveTurbulence.Flower.MkSlots.IntAsm

namespace WaveTurbulence.Flower.MkSlots
open WaveTurbulence.Induct WaveTurbulence.LGSpine

/-- **Deliverable 1**: the corrected α core on the prefix. -/
theorem classRepAlphaJ_prefix (cP : ℝ) (hcP : 37 ≤ cP) (hcap : CapSlotObligation) : WTPrefix (ClassRepAlphaJ cP) :=
  prefix_map (fun _ h => h.2) (IntAsm.classRepAlphaJ_prefixL cP hcP hcap)

/-- **Deliverable 2**: milestone α with `|J| = R` on the prefix. -/
theorem markedClassRepresentsMKαJ_prefix (cP cθ : ℝ) (hcP : 37 ≤ cP) (hcap : CapSlotObligation) :
    WTPrefix (MarkedClassRepresentsMKαJ cP cθ) :=
  prefix_map (fun _ h => markedClassRepresentsMKαJ_of_rep h.1 h.2) (IntAsm.classRepAlphaJ_prefixL cP hcP hcap)

end WaveTurbulence.Flower.MkSlots
