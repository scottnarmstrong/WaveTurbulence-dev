/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegStruct.ReverseRange

/-! # Exact REG-STRUCT decoding obligations used by the B2 instantiation -/

public section
namespace WaveTurbulence.IncohInst

/-- Exact O3. -/
theorem tree_exists_decodes (X : RegChain) (hX : X.wf = true) (ζ : ℤˣ) :
    ∃ G : Garden 1, G.sig 0 = ζ ∧ X.DecodesTree G ∧ IsRegularTree G :=
  Reg.wf_chain_exists_regular_decodesTree X hX ζ

/-- Exact O5. -/
theorem couple_size_eq_order (Q : RegCpl) {G : Garden 2} (h : Q.Decodes G) : G.order = Q.size :=
  Reg.size_eq_order h

end WaveTurbulence.IncohInst
