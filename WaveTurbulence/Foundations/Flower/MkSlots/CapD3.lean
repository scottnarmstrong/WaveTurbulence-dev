/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.Statement
public import WaveTurbulence.Foundations.Flower.ProtWhole.RegBound
public import WaveTurbulence.Foundations.Flower.MkSlots.CapSup

/-! # B3s MK-SLOTS (cap slots): D3's `term` bound for the paired tree of a cap couple, as a superposition

For a cap couple (D6b's `CapG`) whose paired tree `T1` is a protected object (`ProtShape`, `ProtAmbient`), D3's
`ProtBoundNTAt` at `cfg = term`, `θ = η`, `q' = p` bounds the `X^{η,30d,0}` norm of the `term`-pinned protected kernel
on `timeBoxGt p p` (`capTerm_xnorm`). The kernel sees neither its lone-port time (the lone parent, the capped flower
parent, is pinned) nor its pins through the upper clock, and it is continuous in the upper clock (D6b's
`continuous_kernelProt_up`), so `capSup_of_xnorm` turns the bound into a superposition on the whole window
(`capTerm_sup`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtWhole

namespace WaveTurbulence.Flower.MkSlots

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ}

theorem xnormRestr_anti_out {r d : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ)) {K K' : Set (Mom d)}
    (hK : K ⊆ K') (F : (Fin r → ℝ) → Mom d → ℂ) : XNormRestr θ Λ₁ Λ₂ B K F ≤ XNormRestr θ Λ₁ Λ₂ B K' F := by
  unfold XNormRestr
  exact iInf_mono fun G => iInf_mono' fun hG => ⟨fun t ht k hk => hG t ht k (hK hk), le_rfl⟩

end WaveTurbulence.Flower.MkSlots
