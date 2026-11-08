/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTCplObl
public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTGeo4
public import WaveTurbulence.Foundations.Flower.MkSlotsO.Split
public import WaveTurbulence.Foundations.Flower.MkSlots.CapObl

/-! # B3s-HELPER3 (B5(ii), ruling R188): **`rtChainKind`**, **`protCplKind`** from `RootTraceGate`

HELPER8's two root-trace kinds (`MkSlotsO.GenSlotOnAt`, SlotObl rev 4), with `MkSlotsO.RootTraceGate` as the ONE
isolated hypothesis:
* `rtChainKindAt`, **`rtChainKind`**: the chain slots with a pinned native and no stem native (`IsRTChainSlot`) — the
  off-stem root-trace chains (RT (i)), at `θ = η`, never `SelAdj`;
* `protCplKindAt`, **`protCplKind`**: the non-cap leaf pairs with a pinned or selected native (`IsProtCplSlot`) — a
  non-cap couple carries no selected native; with a pinned native it is the off-stem root-trace couple (RT (ii′)), at
  `θ = η` off `SelAdj` and `θ = 1/4` on `SelAdj` (one pinned root).
The geometry (`rtChain_of_pred`, `rtCouple_of_pred`, `not_selNat_cpl`) is in `RTGeo1`–`RTGeo4`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
  WaveTurbulence.VineAlign WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtDefs

namespace WaveTurbulence.Flower.MkSlotsB

theorem layer_le_of_canon {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (hcan : IsCanonGC (p + 1) a.layered) :
    ∀ z, (MkSlots.recLG a).layer z ≤ p := by
  have hrec : MkSlots.recLG a = a.layered := sourceLayer_reconstructs a
  rw [hrec]
  exact hcan.2.2.1

/-- **The root-trace chain kind at one parameter record**, from RT at that record. -/
theorem rtChainKindAt {P : WTParams} (hRT : MkSlotsO.RootTraceBoundAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) :
    MkSlotsO.GenSlotOnAt MkSlotsO.IsRTChainSlot rtKc P := by
  intro C hC R p a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b
    hb1 hb Rf hRf hRf' dag s' sl hsl hQ x
  have hRf1 : ∀ j r, Rf j = some r → 1 ≤ r := fun j r hr => by have := hRf j r hr; linarith
  obtain ⟨γ', rfl, G⟩ := rtChain_of_pred a J pat t s kSel σ hcan hJ hgeo hpat hirr _ hQ.1 hQ.2.1 hQ.2.2
  refine MkSlotsO.slotConcl_of_fam1 P C rtKc a J pat t s σ kSel Rs h roots Rf dag b (.inr γ') x (fun _ => ?_)
    (fun hsa => absurd hsa (G.notSelAdj kSel hkSel))
  exact slotFam1_chain hRT (by omega) hη.le (by linarith) hηγ hC1 hδ C hC hp hsz hs.1 (hs.2.trans ht.2)
    (layer_le_of_canon a hcan) G σ kSel Rs h roots b hb1 hb Rf hRf1 dag x

/-- **The root-trace couple kind at one parameter record**, from RT at that record. -/
theorem protCplKindAt {P : WTParams} (hRT : MkSlotsO.RootTraceBoundAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
    (hη4 : P.η ≤ 1 / 4) (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁)
    (hδ : 0 ≤ P.δ) :
    MkSlotsO.GenSlotOnAt MkSlotsO.IsProtCplSlot rtKcpl P := by
  intro C hC R p a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b
    hb1 hb Rf hRf hRf' dag s' sl hsl hQ x
  have hRf1 : ∀ j r, Rf j = some r → 1 ≤ r := fun j r hr => by have := hRf j r hr; linarith
  rcases hQ.2 with hpin | hsel
  · obtain ⟨q', Rt, rfl, G⟩ := rtCouple_of_pred a J pat t s kSel σ hcan hJ hgeo hpat hirr ht hs _ hQ.1 hpin
    have hgsm := MkSlotsO.genSlotMass_nonneg P (le_trans (le_trans zero_le_one hC1) hC) hb1 (by linarith) a J pat t
      s kSel Rs (fun j => by have := hRs j; linarith) (.inl q')
    refine MkSlotsO.slotConcl_of_fam1 P C rtKcpl a J pat t s σ kSel Rs h roots Rf dag b (.inl q') x
      (fun _ => ?_) (fun hsa => ?_)
    · refine slotFam1_cpl hRT (by omega) (by linarith) hηγ hC1 hδ C hC hp hsz hs.1 (hs.2.trans ht.2)
        (layer_le_of_canon a hcan) G P.η hη.le (Or.inl rfl) σ kSel Rs h roots b hb1 hb Rf hRf1 dag x (rtKcpl P.d P.η)
        ?_ _ le_rfl
      have := rtKq_nonneg P.d (1 / 4)
      unfold rtKcpl rtKq at *
      linarith
    · refine slotFam1_cpl hRT (by omega) (by linarith) hηγ hC1 hδ C hC hp hsz hs.1 (hs.2.trans ht.2)
        (layer_le_of_canon a hcan) G (1 / 4) (by norm_num) (Or.inr ⟨rfl, fun hb2 => G.notSelAdj hb2 kSel hsa⟩)
        σ kSel Rs h roots b hb1 hb Rf hRf1 dag x (rtKcpl P.d P.η) ?_ _ ?_
      · have := rtKq_nonneg P.d P.η
        unfold rtKcpl rtKq at *
        linarith
      · refine ENNReal.ofReal_le_ofReal ?_
        have hK : 0 ≤ rtKcpl P.d P.η := le_trans zero_le_one (one_le_rtKcpl P.d P.η)
        have hLp : 1 ≤ P.L ^ (47 * (P.d : ℝ) + 2) := Real.one_le_rpow (by linarith) (by positivity)
        calc rtKcpl P.d P.η * MkSlotsI.genSlotMass P C b a J pat t s kSel Rs (.inl q')
            = rtKcpl P.d P.η * 1 * MkSlotsI.genSlotMass P C b a J pat t s kSel Rs (.inl q') := by ring
          _ ≤ _ := by gcongr
  · exact absurd hsel (not_selNat_cpl a J pat t s kSel σ _ hQ.1)

/-- **`rtChainKind`** (B5(ii), R188): HELPER8's root-trace chain kind from `RootTraceGate`. -/
theorem rtChainKind (hRT : MkSlotsO.RootTraceGate) :
    ∃ K : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ K d η) ∧ WTPrefix (MkSlotsO.GenSlotOnAt MkSlotsO.IsRTChainSlot K) := by
  refine ⟨rtKc, one_le_rtKc, ?_⟩
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hRT d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1def
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1 : 0 < g1 := by
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  have hg1' : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min η₀ ((g1 / 2) ^ 2), lt_min hη₀ (by positivity), fun η hη φin hφin τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₀ := ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  have hη2 : η ≤ (g1 / 2) ^ 2 := hη.2.trans (min_le_right _ _)
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη1 φin hφin τs hτs φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD hτD
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact rtChainKindAt (H4 L hL) hd hη.1 (MkSlots.sqrt_add_pow8_le hg1 hg1' hη.1 hη2) (le_trans hL₀ hL) hC₁
    hδ.1.le

/-- **`protCplKind`** (B5(ii), R188): HELPER8's protected couple kind from `RootTraceGate`. -/
theorem protCplKind (hRT : MkSlotsO.RootTraceGate) :
    ∃ K : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ K d η) ∧ WTPrefix (MkSlotsO.GenSlotOnAt MkSlotsO.IsProtCplSlot K) := by
  refine ⟨rtKcpl, one_le_rtKcpl, ?_⟩
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hRT d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1def
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1 : 0 < g1 := by
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  have hg1' : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min η₀ (min ((g1 / 2) ^ 2) (1 / 4)), lt_min hη₀ (lt_min (by positivity) (by norm_num)),
    fun η hη φin hφin τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₀ := ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  have hη2 : η ≤ (g1 / 2) ^ 2 := hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη4 : η ≤ 1 / 4 := hη.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη1 φin hφin τs hτs φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD hτD
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact protCplKindAt (H4 L hL) hd hη.1 hη4 (MkSlots.sqrt_add_pow8_le hg1 hg1' hη.1 hη2) (le_trans hL₀ hL) hC₁
    hδ.1.le

end WaveTurbulence.Flower.MkSlotsB
