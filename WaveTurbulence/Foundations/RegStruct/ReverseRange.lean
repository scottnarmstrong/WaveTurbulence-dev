/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OuterDecorations
public import WaveTurbulence.Foundations.RegStruct.DecodedTreeProperties

/-! # Every well-formed code has an actual source-regular decoded carrier

A source-regular bare outer template is constructed by A or B. Every listed
inserted couple has strictly smaller code order. Actual graft closure replaces
all template leaf pairs, retaining the complete oriented pair list. This closes
the converse range without assuming any characterization theorem.
-/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Every well-formed couple code decodes to an actual A/B-generated regular couple. -/
theorem wf_decodedCouple_isRegular (C : RegCpl) (hw : C.wf = true) : IsRegularCouple (decodedCouple C) := by
  generalize hsize : C.size = N
  induction N using Nat.strong_induction_on generalizing C with
  | h N ih =>
    cases C with
    | triv => exact decodedTriv_isRegular
    | type1 c r g d =>
      simp only [RegCpl.wf,Bool.and_eq_true] at hw
      change r.size+g.size+d.size+2 = N at hsize
      have hr := ih r.size (by omega) r hw.1.1 rfl
      have hg := ih g.size (by omega) g hw.1.2 rfl
      have hd := ih d.size (by omega) d hw.2 rfl
      apply isRegularCouple_of_decorated_template (miniCoupleCode c) (.type1 c r g d)
        (type1Decorations c r g d) (miniCouple_isRegular c)
        (List.Perm.of_eq (type1Decorations_frames c r g d).symm) (type1Decorations_pairs c r g d)
      intro e he
      simp only [type1Decorations,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hr
      · exact hg
      · exact hd
    | type2 p n q =>
      apply isRegularCouple_of_decorated_template
        (joinChains (eraseChainCouples p) (eraseChainCouples n) .triv) (.type2 p n q)
        (type2Decorations p n q)
        (bareDoubleChain_isRegular _ _ (eraseChainCouples_bare p) (eraseChainCouples_bare n))
        (List.Perm.of_eq (type2Decorations_frames p n q).symm) (type2Decorations_pairs p n q)
      intro e he
      have hlt := type2Decorations_size_lt p n q hw e he
      have hew := type2Decorations_wf p n q hw e he
      exact ih e.2.size (by omega) e.2 hew rfl

/-- The exact decoding range is the source-regular couples. -/
theorem isRegularCouple_iff_exists_wf_decodes (G : Garden 2) :
    IsRegularCouple G ↔ ∃ C : RegCpl, C.wf = true ∧ C.Decodes G := by
  constructor
  · exact isRegularCouple_exists_wf_decodes G
  · rintro ⟨C,hw,hC⟩
    rw [decodedCouple_unique C G hC]
    exact wf_decodedCouple_isRegular C hw

/-- The actual carrier needed for the B2 couple decoding range obligation. -/
theorem wf_code_exists_regular_decodes (C : RegCpl) (hw : C.wf = true) :
    ∃ G : Garden 2, C.Decodes G ∧ IsRegularCouple G :=
  ⟨decodedCouple C,decodedCouple_decodes C,wf_decodedCouple_isRegular C hw⟩

/-- Every well-formed chain code has an actual source-regular tree carrier at either specified sign. -/
theorem wf_decodedTree_isRegular (X : RegChain) (hw : X.wf = true) (ζ : ℤˣ) :
    IsRegularTree (decodedTree X ζ) :=
  decodedTree_isRegular_of_aux X ζ (wf_decodedCouple_isRegular _ (treeAuxCode_wf X ζ hw))

/-- The exact per-sign actual carrier needed for B2's tree decoding range obligation. -/
theorem wf_chain_exists_regular_decodesTree (X : RegChain) (hw : X.wf = true) (ζ : ℤˣ) :
    ∃ G : Garden 1, G.sig 0 = ζ ∧ X.DecodesTree G ∧ IsRegularTree G :=
  ⟨decodedTree X ζ,decodedTree_sign X ζ,decodedTree_decodes X ζ,wf_decodedTree_isRegular X hw ζ⟩

/-- The tree decoder's range is exactly the source regular trees. -/
theorem isRegularTree_iff_exists_wf_decodesTree (G : Garden 1) :
    IsRegularTree G ↔ ∃ X : RegChain, X.wf = true ∧ X.DecodesTree G := by
  constructor
  · exact isRegularTree_exists_wf_decodes G
  · rintro ⟨X,hw,hX⟩
    rw [decodedTree_unique X (G.sig 0) G hX rfl]
    exact wf_decodedTree_isRegular X hw (G.sig 0)

end WaveTurbulence.Reg
