/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.SelGate
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Couple

/-! # D3 PROT-PIN: `ProtBoundSelGate` (ruling R182)

R182 adds `v ∉ F` to ProtDefs' `ProtBoundSelAt` (after `F`'s scale clause); it is the first disjunct of
`ProtBoundSelDisjAt`'s hypothesis `v ∉ F ∨ v ∉ Fu`, so `protBoundSelGate` follows from `protBoundSelDisjGate`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin.Sel

open WaveTurbulence.Flower.ProtDefs

theorem selAt_of_disj {P : WTParams} (h : ProtBoundSelDisjAt P) : ProtBoundSelAt P := by
  intro p hp n hn w LG X hsh hsz hne hamb v hv0 hvpre hvne hvterm M₂ hM₂ s hps hsp q' hq' S ω cω hpres F M hM hvF
    Fu Mu hMu ind hind H B hH b₀ c₀
  exact h p hp n hn w LG X hsh hsz hne hamb v hv0 hvpre hvne hvterm M₂ hM₂ s hps hsp q' hq' S ω cω hpres F M hM
    Fu Mu hMu (Or.inl hvF) ind hind H B hH b₀ c₀

/-- **`ProtBoundSelGate`** (R181/R182; unconditional). -/
theorem protBoundSelGate : ProtBoundSelGate :=
  protBoundSelDisjGate.mono fun _ h => selAt_of_disj h

example : ProtDefs.ProtBoundSelGate := protBoundSelGate

end WaveTurbulence.Flower.ProtPin.Sel
