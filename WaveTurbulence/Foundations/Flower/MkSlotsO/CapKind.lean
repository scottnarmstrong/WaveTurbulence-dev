/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapPen
public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapTrv

/-! # B3s-HELPER8 / CAP: the cap kind

The slot obligation on the cap pairs (`IsCapSlot`), from D3 (`ProtPin.protBoundGate`) and D6
(`ProtWhole.protAnnBoundGate_of_D3`), with the constant `capKg`:

* **`IsCapPenFree`** (the STOP configuration, `CapK.CapPenFree`, explicitly `CapK.capPenFree_spec`): a nontrivial cap
  couple whose configuration pins the root (`penTerm`: pattern `dParent` on the chain's tree, `|X.lonePath| = 2`) and
  whose chain clock is free (the chain's skeleton leaf is not a skeleton root);
* `capKindAt_off`: the obligation at one parameter record on the cap pairs outside the STOP configuration (trivial cap
  couples: `CapT.capT_concl`; nontrivial: `CapN.capN_concl`);
* **`capKind_off`** `: ∃ K, (∀ d η, 1 ≤ K d η) ∧ WTPrefix (GenSlotOnAt IsCapOffSlot K)`;
* **`capKind_of_penFree`**: the target `capKind` statement, from the obligation on the STOP configuration alone.

Under SlotObl rev 4 the STOP configuration was not derivable: `genBoxAt` contains chain clocks `ts j0 ∈ [p, s)` on
which the relaxed kernel depends on `ts j0`. Rev 5 asks the HasSum only on `genBoxAt ∩ TopCut`, where `s ≤ ts j0`;
the target `capKind` is proved in `CapFinal.lean` (`capKind_pf`, `capKind`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtWhole
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-- **The STOP configuration** of a cap slot: a nontrivial cap couple whose configuration pins the root while its
chain clock is free (`CapK.CapPenFree`; `CapK.capPenFree_spec`: pattern `dParent`, `|X.lonePath| = 2`). -/
def IsCapPenFree : SlotPred := fun a J pat t s _ _ sl =>
  ∃ q, sl = .inl q ∧ ∃ K : CapSide a.prime.data a.prime.prime.1 J q,
    CapK.CapPenFree K (sourceLayer a) (sourceLayer_isLayering a) pat t s

/-- A cap pair outside the STOP configuration. -/
def IsCapOffSlot : SlotPred := fun a J pat t s kSel σ sl =>
  IsCapSlot a J pat t s kSel σ sl ∧ ¬ IsCapPenFree a J pat t s kSel σ sl

/-- **The cap obligation at one parameter record, outside the STOP configuration.** -/
theorem capKindAt_off {P : WTParams} (hD3 : ProtBoundAt P) (hD6 : ProtAnnBoundAt P) (hd : 3 ≤ P.d) (hη : 0 < P.η)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) :
    GenSlotOnAt IsCapOffSlot capKg P := by
  intro C hC R p a J pat t s hp hcan hsz _ hGeo hpat _ ht hs kSel hplain σ Rs hRs _ _ _ roots h b hb1 hb Rf hRf _
    dag _ sl _ hQ x
  obtain ⟨⟨q, rfl, hq⟩, hnot⟩ := hQ
  have hrec : recLG a = a.layered := sourceLayer_reconstructs a
  rw [← hrec] at hcan hGeo hpat
  have hcap : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = .leaf := hGeo.cap_leaf
  have hRf1 : ∀ j r, Rf j = some r → 1 ≤ r := fun j r hr => by have := hRf j r hr; linarith
  rcases capSlot_cases a.prime.data a.prime.prime.1 J hcap q hq with htriv | ⟨X, hX, hne, hQ, h2, h1⟩ |
      ⟨X, hX, hne, hQ, h1, h2⟩
  · exact CapT.capT_concl (hL := hL) (hd := hd) (C := C) (a := a) (J := J) (pat := pat) (t := t) (s := s)
      (hGeo := hGeo) (σ := σ) (kSel := kSel) (Rs := Rs) (roots := roots) (h := h) (b := b) (hb1 := hb1)
      (Rf := Rf) (dag := dag) (hq := hq) (ht := htriv) (x := x)
  · let K := capSideLeft a.prime.data a.prime.prime.1 J q X hX hne hQ h2 h1
    exact CapN.capN_concl (hD3 := hD3) (hD6 := hD6) (hd := hd) (hη := hη) (hηγ := hηγ) (hL := hL) (hC1 := hC1)
      (hδ := hδ) (C := C) (hC := hC) (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan)
      (hsz := hsz) (hGeo := hGeo) (hpat := hpat) (hps := hs.1) (hst := hs.2) (htp := ht.2) (σ := σ) (kSel := kSel)
      (hplain := hplain) (Rs := Rs) (hRs := hRs) (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb)
      (Rf := Rf) (hRf1 := hRf1) (dag := dag) (hq := hq) (K := K) (x := x) (hfree := fun hpf => hnot ⟨q, rfl, K, hpf⟩)
  · let K := capSideRight a.prime.data a.prime.prime.1 J hcap q X hX hne hQ h1 h2
    exact CapN.capN_concl (hD3 := hD3) (hD6 := hD6) (hd := hd) (hη := hη) (hηγ := hηγ) (hL := hL) (hC1 := hC1)
      (hδ := hδ) (C := C) (hC := hC) (a := a) (J := J) (pat := pat) (t := t) (s := s) (hp := hp) (hcan := hcan)
      (hsz := hsz) (hGeo := hGeo) (hpat := hpat) (hps := hs.1) (hst := hs.2) (htp := ht.2) (σ := σ) (kSel := kSel)
      (hplain := hplain) (Rs := Rs) (hRs := hRs) (roots := roots) (h := h) (b := b) (hb1 := hb1) (hb := hb)
      (Rf := Rf) (hRf1 := hRf1) (dag := dag) (hq := hq) (K := K) (x := x) (hfree := fun hpf => hnot ⟨q, rfl, K, hpf⟩)

/-- D6's statement is monotone in the large constants. -/
theorem protAnnBoundAt_mono : LargeConstantMonotone ProtAnnBoundAt := by
  intro P c₁ c₂ hC hC₂ hδ hL hCC hCC₂ h
  exact (protAnnBoundAt_iff_case _).2
    (protAnnCaseAt_mono _ P c₁ c₂ hC hC₂ hδ hL hCC hCC₂ ((protAnnBoundAt_iff_case P).1 h))

/-- **The cap kind outside the STOP configuration**, on the prefix, from D3 and D6. -/
theorem capKind_off : ∃ K : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ K d η) ∧ WTPrefix (GenSlotOnAt IsCapOffSlot K) := by
  refine ⟨capKg, fun d η => one_le_capKg d η, ?_⟩
  have hall : WTPrefix (fun P => ProtBoundAt P ∧ ProtAnnBoundAt P) :=
    prefix_and ProtPin.protBoundGate (protAnnBoundGate_of_D3 ProtPin.protBoundGate) protBoundAt_mono
      protAnnBoundAt_mono
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := hall d hd γ hγ
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
  exact capKindAt_off (H4 L hL).1 (H4 L hL).2 hd hη.1 (sqrt_add_pow8_le hg1 hg1' hη.1 hη2) (le_trans hL₀ hL) hC₁
    hδ.1.le

/-- **The target, from the obligation on the STOP configuration**: with any constant `K'` for the slots
`IsCapPenFree`, the cap kind holds with `max capKg K'`. -/
theorem capKind_of_penFree {K' : ℕ → ℝ → ℝ} (hpf : WTPrefix (GenSlotOnAt IsCapPenFree K')) :
    ∃ K : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ K d η) ∧ WTPrefix (GenSlotOnAt IsCapSlot K) := by
  obtain ⟨K₁, hK₁, h₁⟩ := capKind_off
  refine ⟨fun d η => max (K₁ d η) (K' d η), fun d η => (hK₁ d η).trans (le_max_left _ _), ?_⟩
  refine prefix_genSlotOnAt_or (fun a J pat t s kSel σ sl hcap => ?_) h₁ hpf
  by_cases h : IsCapPenFree a J pat t s kSel σ sl
  · exact Or.inr h
  · exact Or.inl ⟨hcap, h⟩

end WaveTurbulence.Flower.MkSlotsO
