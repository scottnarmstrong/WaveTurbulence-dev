/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildTraceF

/-! # D3 PROT-PIN: the (P7) case handed to the helper D3-HELPER

`tcT2a`: the root-traced side couple is of type 2 with a nonempty chain on the traced tree `0` (o104 Prop 7.4 (a),
`ε = +`; D2c `Root2Data`, `Root2Data.kernelProt_root2`). Target of briefs/D3-HELPER.md:
`∃ Ct, 0 ≤ Ct ∧ TcTraceOnF θ Ct tcT2a` for `0 ≤ θ ≤ 1/4`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- Type 2, traced root of tree `0`, nonempty chain on tree `0` (o104 Prop 7.4 (a), `ε = +`). -/
def tcT2a (Q : RegCpl) (_LGc : LayeredGarden 2) (j : Fin 2) (_p : ℕ) : Prop :=
  j = 0 ∧ ∃ (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest Xm : RegChain) (Qlp : RegCpl),
    Q = RegCpl.type2 (RegChain.pair m Qr Qg inner rest) Xm Qlp

end WaveTurbulence.Flower.ProtPin
