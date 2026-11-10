/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelWeight
public import WaveTurbulence.Foundations.Flower.MkSlotsB.RLeaves
public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapHyp

/-! # B3s-HELPER4 (δ) S3: the selected slots (statement)

A selection absorbed in a slot (S2 case (b)) lies on the lone path of the native object of the slot: the regular chain
`X(β)` inflated at a skeleton branch `β` (slot `.inr β`, no pin of a plain-pattern tree inside) or the cap couple of a
cap pair (slot `.inl q`, the capped flower parent pinned at `s`). Its weight inside the slot is the per-slot factor
`selΘs` of the β reduction (`MkSlotsB.slotFnGWFR`, weight `(∏ W) · Θ · ∏_s Θs s`): the product over the non-core
native nodes of the selection node weight `selNW` (the selected filter `chiD(|Ω|/Rs j)` at the selected vertex, the
shells `χ₀(|Ω|/Rs j)` at the other stem nodes), with `Ω` computed in the native garden at the slot momentum (for a
non-core native branch its three children are native nodes). This is the slot part of S4's partition
(`selWeight_split`, `slotFac`).

* `omegaAt`, `selNW` (`selNW_toNode`: on branches it is S4's `selBW`), `HasSelNative`, `selΘs`;
* `selSlotKer`: the pinned weighted slot kernel of the reconstruction of a prescribed point with the selection factor
  (as B3s's `capSlotKer`, on β's relaxed `slotFnGWFR` with `Θs = selΘs`);
* **`SelSlotObligationAt Kc P`**, **`SelSlotObligation`**: for every slot of the reconstruction containing a selected
  native node, on the slot box, a superposition of Fourier modes with `SlotFam`-compatible amplitudes (at every slot
  momentum for a chain slot, at the cap momentum for a cap pair, as `MkSlots.CapSlotObligationAt`), with mass the B3
  slot mass × the protected loss `L^{2(47d+5)}` (D6's `L^{(47d+5)r}`, `r = pin + #Sel ≤ 2`) × the gain
  `∏ Rs_j^{-1/18}` over the selected native vertices of the slot (D6's `M₂^{-a/18}`, `a ≤ 1` per object).

STATUS: statement only (the proof from `ProtWhole.protAnnBoundGate_of_D3` is open; see `HANDOFF.md`, S3). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlots
open WaveTurbulence.Flower.MkSlotsT (radProd)

namespace WaveTurbulence.Flower.MkSlotsS

variable {w d : ℕ}

/-- The resonance factor at a node (`0` at a leaf). -/
def omegaAt {w' : ℕ} {G : Garden w'} (k : GNode G.tree → Mom d) (a : GNode G.tree) : ℝ :=
  if h : a.1.2 ∈ (G.tree a.1.1).branching then omegaNode G k ⟨a.1, h⟩ else 0

section Slots

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-- The slot `sl` of the reconstruction contains a selected vertex as a non-core native node. -/
def HasSelNative (sl : ReplacementSlot S) : Prop :=
  ∃ a : NativeNode D sl, (∀ β : GBranch S.tree, nativeNodeAt D hS sl a ≠ (D.coreBranch hS β).toNode) ∧
    ∃ v ∈ selSetCap (layeredReconstruction D hS layer hLayer) J kSel, v.1 = (nativeNodeAt D hS sl a).1

/-- The selected vertices of the reconstruction that are non-core native nodes of the slot `sl`. -/
def selNative (sl : ReplacementSlot S) : Finset (GBranch (layeredReconstruction D hS layer hLayer).garden.tree) :=
  (selSetCap (layeredReconstruction D hS layer hLayer) J kSel).filter fun v =>
    ∃ a : NativeNode D sl, (∀ β : GBranch S.tree, nativeNodeAt D hS sl a ≠ (D.coreBranch hS β).toNode) ∧
      v.1 = (nativeNodeAt D hS sl a).1

end Slots

end WaveTurbulence.Flower.MkSlotsS
