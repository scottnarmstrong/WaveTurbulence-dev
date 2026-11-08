/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.UnSlot
public import WaveTurbulence.Foundations.Flower.FiltGate.Gate
public import WaveTurbulence.Foundations.Flower.FiltCoh.GateD5
public import WaveTurbulence.Foundations.Flower.MkSlots.CapObl

/-! # B3s-HELPER8 / UNPIN: **`unpinKind`** — the slot obligation on the unpinned slots

`IsUnpinSlot` (`MkSlotsO.Split`): not a cap pair, no pinned native branch, no selected native vertex. On such a slot
`MkSlotsI.genSlotKer` is the leafwise kernel of the native object with the INC-TOP star weights of the frontier cutoffs
and two filter layers (σ's dyadic filters, δ's selection shells; none on a couple), and D5's gates
(`FiltGate.filtIncoherentDecayGate`, `FiltCoh.filtCoherentBoundGate`, couples in both orientations through
`ProtPin.tc_coh_any`) give the moment bounds at `θ = η` (no loss) and at `θ = 1/4` (loss `L^{4d} ≤ L^{47d+2}`):

* `filtIncoherentDecayAt_mono`, `filtCoherentBoundAt_mono`: large-constant monotonicity of the D5 gates;
* `Kunp`: the constant `max 1 (max (Kun d η) (Kun d (1/4)))`;
* `genSlotOnAt_unpin_of`: one parameter record;
* **`unpinKind`**: the prefix. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-- Large-constant monotonicity of D5's incoherent gate. -/
theorem filtIncoherentDecayAt_mono : LargeConstantMonotone ProtDefs.FiltIncoherentDecayAt := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource p hp n hn θ c hθc
  rw [LGSpine.N_largeConstants] at hn
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  obtain ⟨h1, h2⟩ := hsource p hp n hn θ c hθc
  constructor
  · intro Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi S ω cω hpres F ann M hM Fu Mu hMu H B hb
    refine (h1 Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi S ω cω hpres F ann M hM Fu Mu hMu H B hb).trans ?_
    gcongr
    exact regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _
  · intro X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi S ω cω hpres F ann M hM Fu Mu hMu H B hb
    refine (h2 X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi S ω cω hpres F ann M hM Fu Mu hMu H B hb).trans ?_
    gcongr
    exact regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _

/-- Large-constant monotonicity of D5's coherent gate. -/
theorem filtCoherentBoundAt_mono : LargeConstantMonotone ProtDefs.FiltCoherentBoundAt := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource p hp n hn θ hθ0 hθ1
  rw [LGSpine.N_largeConstants] at hn
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  obtain ⟨h1, h2⟩ := hsource p hp n hn θ hθ0 hθ1
  constructor
  · intro Q LG q q' hqq hqp hsize hQc S ω cω hpres F ann M hM Fu Mu hMu H B hb
    refine (h1 Q LG q q' hqq hqp hsize hQc S ω cω hpres F ann M hM Fu Mu hMu H B hb).trans ?_
    gcongr
    exact regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _
  · intro X LG q q' hqq hqp hsize hXc S ω cω hpres F ann M hM Fu Mu hMu H B hb
    refine (h2 X LG q q' hqq hqp hsize hXc S ω cω hpres F ann M hM Fu Mu hMu H B hb).trans ?_
    gcongr
    exact regBound_largeConstants_mono P hc0 hCC hδ.le hL0 n _

/-- **The constant of the unpinned kind.** -/
def Kunp (d : ℕ) (η : ℝ) : ℝ := max 1 (max (Kun d η) (Kun d (1 / 4)))

theorem one_le_Kunp (d : ℕ) (η : ℝ) : 1 ≤ Kunp d η := le_max_left _ _

/-- **The unpinned kind at one parameter record.** -/
theorem genSlotOnAt_unpin_of {P : WTParams} (hI : ProtDefs.FiltIncoherentDecayAt P)
    (hC : ProtDefs.FiltCoherentBoundAt P) (hd : 1 ≤ P.d) (hL : 2 ≤ P.L) (hη0 : 0 ≤ P.η) (hη4 : P.η ≤ 1 / 4)
    (hc1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hκ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) :
    GenSlotOnAt IsUnpinSlot Kunp P := by
  intro C hCC R p a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF hfine hclean roots h b
    hb hh Rf hRf hRf' dag s' sl hsl hQ x
  obtain ⟨hncap, hpin, hselN⟩ := hQ
  have hL0 : 0 < P.L := by linarith
  have hL1 : 1 ≤ P.L := by linarith
  have hM0 : 0 ≤ genSlotMass P C b a J pat t s kSel Rs sl :=
    genSlotMass_nonneg P (by linarith) hb hL0 a J pat t s kSel Rs (fun j => lt_of_lt_of_le hL0 (hRs j)) sl
  have hfam : ∀ {θ c : ℝ}, ThetaC P θ c →
      SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag sl x θ
        (ENNReal.ofReal (Kun P.d θ * P.L ^ c * genSlotMass P C b a J pat t s kSel Rs sl)) := by
    intro θ c hθ
    cases sl with
    | inl q =>
      exact unSlot_cpl hI hC hd hL hη0 hη4 hc1 hδ hκ hθ C hCC a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs σ kSel
        Rs roots h b hb hh Rf hRf dag q (fun hq => hncap ⟨q, rfl, hq⟩) hpin hselN x
    | inr β =>
      exact unSlot_chain hI hC hd hL hη0 hη4 hc1 hδ hκ hθ C hCC a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs σ kSel
        Rs hRs roots h b hb hh Rf hRf dag β hpin hselN x
  refine slotConcl_of_fam1 P C Kunp (p := p) a J pat t s σ kSel Rs h roots Rf dag b sl x (fun _ => ?_) (fun _ => ?_)
  · refine slotFam1_mono P (hfam (Or.inl ⟨rfl, rfl⟩)) (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.rpow_zero, mul_one]
    exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hM0
  · refine slotFam1_mono P (hfam (Or.inr ⟨rfl, rfl⟩)) (ENNReal.ofReal_le_ofReal ?_)
    have hK : Kun P.d (1 / 4) ≤ Kunp P.d P.η := (le_max_right _ _).trans (le_max_right _ _)
    have hpow : P.L ^ (4 * (P.d : ℝ)) ≤ P.L ^ (47 * (P.d : ℝ) + 2) := by
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      have : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
      linarith
    have hK0 : 0 ≤ Kun P.d (1 / 4) := Kun_nonneg _ _
    have hpow0 : 0 ≤ P.L ^ (4 * (P.d : ℝ)) := Real.rpow_nonneg hL0.le _
    calc Kun P.d (1 / 4) * P.L ^ (4 * (P.d : ℝ)) * genSlotMass P C b a J pat t s kSel Rs sl
        ≤ Kunp P.d P.η * P.L ^ (47 * (P.d : ℝ) + 2) * genSlotMass P C b a J pat t s kSel Rs sl := by
          gcongr
          exact le_trans zero_le_one (one_le_Kunp _ _)

/-- **`unpinKind`**: the slot obligation on the unpinned slots, unconditionally (D5's gates). -/
theorem unpinKind : ∃ K : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ K d η) ∧ WTPrefix (GenSlotOnAt IsUnpinSlot K) := by
  refine ⟨Kunp, one_le_Kunp, ?_⟩
  have hgate := prefix_and FiltGate.filtIncoherentDecayGate FiltCoh.filtCoherentBoundGate
    filtIncoherentDecayAt_mono filtCoherentBoundAt_mono
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hgate d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1def
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1 : 0 < g1 := by
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  have hg1' : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min η₀ (min (1 / 4) ((g1 / 2) ^ 2)), lt_min hη₀ (lt_min (by norm_num) (by positivity)),
    fun η hη φin hφin τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₀ := ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  have hη4 : η ≤ 1 / 4 := hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη2 : η ≤ (g1 / 2) ^ 2 := hη.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη1 φin hφin τs hτs φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD hτD
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  obtain ⟨hIP, hCP⟩ := H4 L hL
  exact genSlotOnAt_unpin_of hIP hCP (by show 1 ≤ d; omega) (le_trans hL₀ hL) hη.1.le hη4 hC₁ hδ.1.le
    (MkSlots.sqrt_add_pow8_le hg1 hg1' hη.1 hη2)

end WaveTurbulence.Flower.MkSlotsO
