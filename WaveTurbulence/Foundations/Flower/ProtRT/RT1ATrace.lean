/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtRT.RT1A

/-! # RT-GATE (ii), shape (a+): `rt1a_trace`

`RtOneOn θ c' Ct rtT2a`: the one-pinned root trace of the couples `Q = type2 (pair m Qr Qg inner rest) Xm Qlp` traced at
the root of tree `0`, partner window `q'`, piece loss `c'` (D3-HELPER's `tc2a_trace`, ProtPin/TChild2ATrace.lean,
sha256 ac77c339…, generalized). The pieces exist (`tc2a_exists`, `PairOnly.exists_of_wf`); `rt1a_core` gives the
bound. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- **The one-pinned root trace of a type-2 couple with a nonempty `+` chain** (shape (a+)). -/
theorem rt1a_trace {θ c' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (_hc' : 0 ≤ c') :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ RtOneOn θ c' Ct rtT2a := by
  obtain ⟨C, hC, hcore⟩ := rt1a_core hθ0 hθ1
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro P C₁a C₂a C₁b C₂b K hFC _ hθc p hp nr hn Q LGc hwf hsz hdec hle j hCnd q' hq' hamb hj _ hr s hps hsp
    Hc Bc hHc S ω cω hpres F M hM Fu Mu hMu k
  obtain ⟨rfl, m, Qr, Qg, inner, rest, Xm, Qlp, rfl⟩ := hCnd
  obtain ⟨LGZ, LGB, D, hwZ, -, hdB, hsZ⟩ := tc2a_exists LGc m Qr Qg inner rest Xm Qlp hdec hwf
  obtain ⟨LGi, LGr, LGg, Pp⟩ := PairOnly.exists_of_wf LGZ m Qr Qg inner D.decZ hwZ
  have hamb' : MkSlotsO.CplAmbient p p q' (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp) LGc := by
    simpa [rtWin] using hamb
  have hr' : layerAt LGc ((1 : Fin 2), []) ≤ q' := by simpa [t1sw] using hr
  refine (hcore K hFC hθc hp hn D Pp hdB hsZ hwf hsz hdec hle hq' hamb' hj hr' hps hsp Hc Bc hHc S ω cω hpres
    F M hM Fu Mu hMu k).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC.ne]

end WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtRT in
/-- The target of fork E, verbatim. -/
example {θ c' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 4) (hc' : 0 ≤ c') : ∃ Ct : ℝ, 0 ≤ Ct ∧ RtOneOn θ c' Ct rtT2a :=
  rt1a_trace hθ0 hθ1 hc'
