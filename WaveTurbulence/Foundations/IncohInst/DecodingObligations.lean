/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegStruct.ReverseRange

/-! # Exact REG-STRUCT decoding obligations used by the B2 instantiation -/

public section
namespace WaveTurbulence.IncohInst

/-- Exact O1, proved by REG-STRUCT rather than imported from the unfinished anchor. -/
theorem couple_exists_decodes (Q : RegCpl) (hQ : Q.wf = true) :
    ∃ G : Garden 2, Q.Decodes G ∧ IsRegularCouple G :=
  Reg.wf_code_exists_regular_decodes Q hQ

/-- Exact O2. -/
theorem couple_unique_decodes (G : Garden 2) (hG : IsRegularCouple G) :
    ∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G := by
  obtain ⟨Q, hQ, hu⟩ := Reg.isRegularCouple_existsUnique_structure G hG
  exact ⟨Q.1, ⟨Q.2, hQ⟩, fun C hC => congrArg Subtype.val (hu ⟨C, hC.1⟩ hC.2)⟩

/-- Exact O3. -/
theorem tree_exists_decodes (X : RegChain) (hX : X.wf = true) (ζ : ℤˣ) :
    ∃ G : Garden 1, G.sig 0 = ζ ∧ X.DecodesTree G ∧ IsRegularTree G :=
  Reg.wf_chain_exists_regular_decodesTree X hX ζ

/-- Exact O4. -/
theorem tree_unique_decodes (G : Garden 1) (hG : IsRegularTree G) :
    ∃! X : RegChain, X.wf = true ∧ X.DecodesTree G := by
  obtain ⟨X, hX, hu⟩ := Reg.isRegularTree_existsUnique_structure G hG
  exact ⟨X.1, ⟨X.2, hX⟩, fun Y hY => congrArg Subtype.val (hu ⟨Y, hY.1⟩ hY.2)⟩

/-- Exact O5. -/
theorem couple_size_eq_order (Q : RegCpl) {G : Garden 2} (h : Q.Decodes G) : G.order = Q.size :=
  Reg.size_eq_order h

end WaveTurbulence.IncohInst
