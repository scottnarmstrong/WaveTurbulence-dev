/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2A

/-! # D3-HELPER (P7), shape (a+): the target `tc2a_trace`

`TcTraceOnF θ Ct tcT2a`: the root trace bound for the traced couples `Q = type2 (pair m Qr Qg inner rest) Xm Qlp`
traced at the root of tree `0` (o104 Prop 7.4 (a), `ε = +`). The pieces exist (`tc2a_exists`,
`PairOnly.exists_of_wf`) and `tc2a_core` gives the bound. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **The root trace of a type-2 side couple with a nonempty chain on the traced tree** (D3-HELPER target). -/
theorem tc2a_trace {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) : ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT2a := by
  obtain ⟨C, hC, hcore⟩ := tc2a_core hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC _ hθc p hp nr hn Q LGc hwf hsz hdec hle hamb j hj _ hCnd s hps hsp Hc Bc hHc S ω
    cω hpres F M hM Fu Mu hMu k
  obtain ⟨rfl, m, Qr, Qg, inner, rest, Xm, Qlp, rfl⟩ := hCnd
  obtain ⟨LGZ, LGB, D, hwZ, -, hdB, hsZ⟩ := tc2a_exists LGc m Qr Qg inner rest Xm Qlp hdec hwf
  obtain ⟨LGi, LGr, LGg, Pp⟩ := PairOnly.exists_of_wf LGZ m Qr Qg inner D.decZ hwZ
  refine (hcore K hFC hθc hp hn D Pp hdB hsZ hwf hsz hdec hle hamb hj hps hsp Hc Bc hHc S ω cω hpres F M hM Fu Mu
    hMu k).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne]

end WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtPin in
/-- The target of briefs/D3-HELPER.md, verbatim. -/
example {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) : ∃ Ct : ℝ, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT2a :=
  tc2a_trace hθ0 hθ1
