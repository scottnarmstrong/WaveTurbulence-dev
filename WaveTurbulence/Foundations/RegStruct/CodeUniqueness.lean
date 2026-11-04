/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CoupleUniquenessStep

/-! # Uniqueness of all well-formed regular-couple structure data

Both halves are proved simultaneously from actual subtree extractions and
pair-block inclusions. The induction hypotheses are produced at smaller code
orders; no source regularity, characterization, or uniqueness is assumed.
-/

public section
namespace WaveTurbulence.Reg

/-- Simultaneous uniqueness of couples and embedded chains at every order. -/
theorem code_unique_bounded (N : ℕ) : CoupleUniqueUpTo N ∧ ChainUniqueUpTo N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have hchain := chain_unique_induction_step N ih
    exact ⟨couple_unique_induction_step N ih hchain,hchain⟩

/-- Every component of well-formed couple structure data is determined by its actual carrier. -/
theorem wf_code_unique {C D : RegCpl} (hC : C.wf = true) (hD : D.wf = true)
    (he : decodedCouple C = decodedCouple D) : C = D :=
  (code_unique_bounded C.size).1 C D le_rfl hC hD he

/-- Any two well-formed codes decoding the same garden agree in all data. -/
theorem wf_decodes_unique {C D : RegCpl} {G : Garden 2} (hC : C.wf = true) (hD : D.wf = true)
    (hCG : C.Decodes G) (hDG : D.Decodes G) : C = D :=
  wf_code_unique hC hD ((decodedCouple_unique C G hCG).symm.trans (decodedCouple_unique D G hDG))

/-- B2 decoding is injective on well-formed couple codes. -/
theorem decodedCouple_wf_injective :
    Function.Injective (fun C : {C : RegCpl // C.wf = true} => decodedCouple C.1) := by
  intro C D he
  exact Subtype.ext (wf_code_unique C.2 D.2 he)

/-- TARGET's regular-couple structure theorem: every actual source-regular couple
has exactly one well-formed complete set of structure data. -/
theorem isRegularCouple_existsUnique_structure (G : Garden 2) (hG : IsRegularCouple G) :
    ∃! C : {C : RegCpl // C.wf = true}, C.1.Decodes G := by
  obtain ⟨C,hw,hC⟩ := isRegularCouple_exists_wf_decodes G hG
  refine ⟨⟨C,hw⟩,hC,fun D hD => ?_⟩
  exact Subtype.ext (wf_decodes_unique D.2 hw hD hC)

end WaveTurbulence.Reg
