/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.Obl

/-! # B3s-HELPER8: the four work kinds of outer slots and the final assembly

The outer slots are split by their native content (the pins `fixCap … pat` on native branches, δ's selected native
vertices):

* **`IsCapSlot`** — cap pairs (β's B5(i) chain extended by filters, selections and `θ = 1/4`);
* **`IsUnpinSlot`** — not a cap pair, no pinned native branch, no selected native vertex (plain and filtered chains,
  nil chains, plain non-cap couples: B3 / D5);
* **`IsProtChainSlot`** — a chain slot with a pinned native branch or a selected native vertex (D3 `root`/`term`,
  D6 `none`+`Sel`, and the off-stem root trace, `RootTraceGate` (i));
* **`IsProtCplSlot`** — a non-cap leaf pair with a pinned native branch or a selected native vertex (the off-stem
  root traces of couples, `RootTraceGate` (ii′); a selected native vertex does not occur there).

* `HasPinNative`, `HasSelNat`, the four predicates, `slot_split`;
* the protected chains split further (`HasStemNative`): **`IsRTChainSlot`** (off-stem root traces, HELPER3 from
  `RootTraceGate` (i)) and **`IsStemProtChainSlot`** (D3 `root`/`term`, D6), `protChain_split`, `protChainKind_of`;
* **`genSlotObligation_of_split`**: the four prefix results give `MkSlotsI.GenSlotObligation`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs
open WaveTurbulence.Flower.MkSlots (recLG IsCapPair fixNative)
open WaveTurbulence.Flower.MkDefs (OnCapStem)
open WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-- The slot has a native branch pinned by the intrinsic pins `fixCap … pat` (the pins of `genSlotKer`). -/
def HasPinNative : SlotPred := fun a J pat t s _ _ sl =>
  ∃ qb : NativeClockBranch a.prime.data sl,
    (fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) sl qb).isSome

/-- The slot has a selected vertex as a non-core native node (δ's `MkSlotsS.HasSelNative`). -/
def HasSelNat : SlotPred := fun a J _ _ _ kSel _ sl =>
  MkSlotsS.HasSelNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel sl

/-- Not a cap pair, no pinned native branch, no selected native vertex. -/
def IsUnpinSlot : SlotPred := fun a J pat t s kSel σ sl =>
  ¬ IsCapSlot a J pat t s kSel σ sl ∧ ¬ HasPinNative a J pat t s kSel σ sl ∧ ¬ HasSelNat a J pat t s kSel σ sl

/-- A chain slot with a pinned native branch or a selected native vertex. -/
def IsProtChainSlot : SlotPred := fun a J pat t s kSel σ sl =>
  (∃ β, sl = .inr β) ∧ (HasPinNative a J pat t s kSel σ sl ∨ HasSelNat a J pat t s kSel σ sl)

/-- A non-cap leaf pair with a pinned native branch or a selected native vertex. -/
def IsProtCplSlot : SlotPred := fun a J pat t s kSel σ sl =>
  IsCplSlot a J pat t s kSel σ sl ∧ (HasPinNative a J pat t s kSel σ sl ∨ HasSelNat a J pat t s kSel σ sl)

/-- The slot has a non-core native node on a capped stem. -/
def HasStemNative : SlotPred := fun a J _ _ _ _ _ sl =>
  ∃ y : NativeNode a.prime.data sl,
    (∀ β : GBranch a.prime.skeleton.tree, nativeNodeAt a.prime.data a.prime.prime.1 sl y ≠
      (a.prime.data.coreBranch a.prime.prime.1 β).toNode) ∧
    ∃ z : GNode (recLG a).garden.tree, OnCapStem (recLG a) J z ∧
      z.1 = (nativeNodeAt a.prime.data a.prime.prime.1 sl y).1

/-- **An off-stem root-trace chain slot**: a chain slot with a pinned native branch and no native stem node (the
`dChild`-pinned root of a chain hanging at a core capped flower parent; delivered by HELPER3 from `RootTraceGate`). -/
def IsRTChainSlot : SlotPred := fun a J pat t s kSel σ sl =>
  (∃ β, sl = .inr β) ∧ HasPinNative a J pat t s kSel σ sl ∧ ¬ HasStemNative a J pat t s kSel σ sl

/-- **A stem-protected chain slot**: a protected chain slot that is not an off-stem root trace (`dRoot` root chains,
`dParent` F-H3-3 chains, absorbed selections; D3 / D6). -/
def IsStemProtChainSlot : SlotPred := fun a J pat t s kSel σ sl =>
  IsProtChainSlot a J pat t s kSel σ sl ∧ ¬ IsRTChainSlot a J pat t s kSel σ sl

/-- The protected chain slots split into root traces and stem-protected ones. -/
theorem protChain_split {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ) (sl : ReplacementSlot a.prime.skeleton)
    (h : IsProtChainSlot a J pat t s kSel σ sl) :
    IsRTChainSlot a J pat t s kSel σ sl ∨ IsStemProtChainSlot a J pat t s kSel σ sl := by
  by_cases hr : IsRTChainSlot a J pat t s kSel σ sl
  · exact Or.inl hr
  · exact Or.inr ⟨h, hr⟩

/-- The protected chain kind from its two parts. -/
theorem protChainKind_of {K₁ K₂ : ℕ → ℝ → ℝ} (h₁ : WTPrefix (GenSlotOnAt IsRTChainSlot K₁))
    (h₂ : WTPrefix (GenSlotOnAt IsStemProtChainSlot K₂)) :
    WTPrefix (GenSlotOnAt IsProtChainSlot (fun d η => max (K₁ d η) (K₂ d η))) :=
  prefix_genSlotOnAt_or (fun a J pat t s kSel σ sl h => protChain_split a J pat t s kSel σ sl h) h₁ h₂

/-- The four work kinds cover every slot. -/
theorem slot_split {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ) (sl : ReplacementSlot a.prime.skeleton) :
    (IsCapSlot a J pat t s kSel σ sl ∨ IsUnpinSlot a J pat t s kSel σ sl) ∨
      (IsProtChainSlot a J pat t s kSel σ sl ∨ IsProtCplSlot a J pat t s kSel σ sl) := by
  by_cases hcap : IsCapSlot a J pat t s kSel σ sl
  · exact Or.inl (Or.inl hcap)
  by_cases hp : HasPinNative a J pat t s kSel σ sl ∨ HasSelNat a J pat t s kSel σ sl
  · refine Or.inr ?_
    cases sl with
    | inl q =>
      refine Or.inr ⟨⟨q, rfl, fun hq => hcap ⟨q, rfl, hq⟩⟩, hp⟩
    | inr β => exact Or.inl ⟨⟨β, rfl⟩, hp⟩
  · exact Or.inl (Or.inr ⟨hcap, fun h => hp (Or.inl h), fun h => hp (Or.inr h)⟩)

/-- **The obligation from the four work kinds.** -/
theorem genSlotObligation_of_split {K₁ K₂ K₃ K₄ : ℕ → ℝ → ℝ} (hK₁ : ∀ d η, 1 ≤ K₁ d η)
    (hcap : WTPrefix (GenSlotOnAt IsCapSlot K₁)) (hun : WTPrefix (GenSlotOnAt IsUnpinSlot K₂))
    (hpc : WTPrefix (GenSlotOnAt IsProtChainSlot K₃)) (hpq : WTPrefix (GenSlotOnAt IsProtCplSlot K₄)) :
    GenSlotObligation := by
  refine ⟨fun d η => max (max (K₁ d η) (K₂ d η)) (max (K₃ d η) (K₄ d η)),
    fun d η => (hK₁ d η).trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  have h12 := prefix_genSlotOnAt_or (Q := fun a J pat t s kSel σ sl =>
    IsCapSlot a J pat t s kSel σ sl ∨ IsUnpinSlot a J pat t s kSel σ sl) (fun _ _ _ _ _ _ _ _ h => h) hcap hun
  have h34 := prefix_genSlotOnAt_or (Q := fun a J pat t s kSel σ sl =>
    IsProtChainSlot a J pat t s kSel σ sl ∨ IsProtCplSlot a J pat t s kSel σ sl) (fun _ _ _ _ _ _ _ _ h => h)
    hpc hpq
  have hall := prefix_genSlotOnAt_or (Q := fun _ _ _ _ _ _ _ _ => True)
    (fun a J pat t s kSel σ sl _ => slot_split a J pat t s kSel σ sl) h12 h34
  exact prefix_guard hall fun P _ _ _ H => (genSlotObligationAt_iff_on _ P).2 H

end WaveTurbulence.Flower.MkSlotsO
