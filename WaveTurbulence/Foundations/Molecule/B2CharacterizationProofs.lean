/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ReverseRange

/-! # Exact proofs of the five pinned B2 section-4 characterization obligations

The declaration types below are the source-authorized B2 snapshot-1 statements.
This scratch module supplies their actual proofs without importing the original
unfinished section. Definitions remain those of the pinned sections 1–3.
-/

public section
namespace WaveTurbulence

/-- Decoding a well-formed code gives a regular couple carrier. -/
theorem RegCpl.exists_decodes (Q : RegCpl) (hQ : Q.wf = true) :
    ∃ G : Garden 2, Q.Decodes G ∧ IsRegularCouple G :=
  Reg.wf_code_exists_regular_decodes Q hQ

/-- Structure theorem for source-regular couples, with every component of the data unique. -/
theorem existsUnique_regCpl_decodes (G : Garden 2) (hG : IsRegularCouple G) :
    ∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G := by
  obtain ⟨Q,hQ,hunique⟩ := Reg.isRegularCouple_existsUnique_structure G hG
  refine ⟨Q.1,⟨Q.2,hQ⟩,?_⟩
  intro C hC
  exact congrArg Subtype.val (hunique ⟨C,hC.1⟩ hC.2)

/-- Decoding well-formed chain data gives an actual regular tree of either specified sign. -/
theorem RegChain.exists_decodesTree (X : RegChain) (hX : X.wf = true) (ζ : ℤˣ) :
    ∃ G : Garden 1, G.sig 0 = ζ ∧ X.DecodesTree G ∧ IsRegularTree G :=
  Reg.wf_chain_exists_regular_decodesTree X hX ζ

/-- Structure theorem for source-regular trees, with every chain and side-couple datum unique. -/
theorem existsUnique_regChain_decodesTree (G : Garden 1) (hG : IsRegularTree G) :
    ∃! X : RegChain, X.wf = true ∧ X.DecodesTree G := by
  obtain ⟨X,hX,hunique⟩ := Reg.isRegularTree_existsUnique_structure G hG
  refine ⟨X.1,⟨X.2,hX⟩,?_⟩
  intro Y hY
  exact congrArg Subtype.val (hunique ⟨Y,hY.1⟩ hY.2)

/-- The code size equals the actual decoded branching order. -/
theorem RegCpl.size_eq_order (Q : RegCpl) {G : Garden 2} (h : Q.Decodes G) : G.order = Q.size :=
  Reg.size_eq_order h

end WaveTurbulence
