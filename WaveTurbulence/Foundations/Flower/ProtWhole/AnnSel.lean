/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.AnnPin
public import WaveTurbulence.Foundations.Flower.ProtPin.SelExact

/-! # D6b: `ProtAnnBoundGate` with D3's selected-vertex gate discharged

D3 proved `ProtBoundSelGate` (world `ProtPin/SelExact.lean`, `ProtPin.Sel.protBoundSelGate`; ProtDefs 75a2c0b6, R181/R182).
`annPin_of` instantiates it with `F \ Sel = F.erase v` (so `v ∉ F` holds by `Finset.notMem_erase`). What remains is
D3's `ProtBoundGate` and the unpinned selected case `ProtAnnFreeSelAt` (finding F-D6b-4). This module is separate so
that the rest of ProtWhole does not import the ProtPin area. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.Flower.ProtWhole

open WaveTurbulence.Flower.ProtDefs

/-- **`ProtAnnBoundGate`** from D3's `ProtBoundGate` and the unpinned selected case. -/
theorem protAnnBoundGate_of_free (hD3 : ProtBoundGate) (hfree : WTPrefix ProtAnnFreeSelAt) : ProtAnnBoundGate :=
  protAnnBoundGate_of_sel hD3 ProtPin.Sel.protBoundSelGate hfree

example : ProtBoundGate → WTPrefix ProtAnnFreeSelAt → ProtAnnBoundGate := protAnnBoundGate_of_free

end WaveTurbulence.Flower.ProtWhole

#print axioms WaveTurbulence.Flower.ProtWhole.protAnnBoundGate_of_free
