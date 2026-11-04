/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.SourceRegularDecoding
public import WaveTurbulence.Foundations.RegStruct.CarrierUniqueness
public import WaveTurbulence.Foundations.RegStruct.CodeCount

/-! # Exponential counting of actual source-regular couples

Every source object has well-formed data, and a fixed code determines one
carrier. Choosing such data embeds the actual source objects in the finite
code set. Injectivity of decoding in the opposite direction is not needed
for this upper bound and is not asserted here.
-/

@[expose] public section
namespace WaveTurbulence.Reg

/-- Actual regular couple carriers of the specified branching order. -/
abbrev SourceCouples (m : ℕ) := {G : Garden 2 // IsRegularCouple G ∧ G.order = 2*m}

/-- Choose data produced by the source construction-history theorem. -/
noncomputable def sourceCoupleCode (m : ℕ) (G : SourceCouples m) :
    {Q : RegCpl // Q.wf = true ∧ Q.size = 2*m} := by
  classical
  let h := isRegularCouple_exists_wf_decodes G.1 G.2.1
  let Q := Classical.choose h
  have hQ := Classical.choose_spec h
  exact ⟨Q,hQ.1,(size_eq_order hQ.2).symm.trans G.2.2⟩

/-- The chosen data decode the original actual carrier. -/
theorem sourceCoupleCode_decodes (m : ℕ) (G : SourceCouples m) :
    (sourceCoupleCode m G).1.Decodes G.1 := by
  exact (Classical.choose_spec (isRegularCouple_exists_wf_decodes G.1 G.2.1)).2

/-- Distinct actual source objects receive distinct structure data. -/
theorem sourceCoupleCode_injective (m : ℕ) : Function.Injective (sourceCoupleCode m) := by
  intro G H he
  apply Subtype.ext
  have hG := sourceCoupleCode_decodes m G
  have hH := sourceCoupleCode_decodes m H
  rw [← he] at hH
  exact carrier_unique hG hH

/-- The finite set of codes of a given order. -/
theorem finite_coupleCodes (m : ℕ) : Finite {Q : RegCpl // Q.wf = true ∧ Q.size = 2*m} :=
  Finite.of_injective (fun Q => wordSlots (8*m+1) (boundedCoupleWord m Q))
    ((wordSlots_injective _).comp (boundedCoupleWord_injective m))

/-- There are finitely many actual regular couples at each order. -/
theorem finite_sourceCouples (m : ℕ) : Finite (SourceCouples m) := by
  let _ := finite_coupleCodes m
  exact Finite.of_injective (sourceCoupleCode m) (sourceCoupleCode_injective m)

/-- Number of actual source-regular couples of order `2m`. -/
noncomputable def sourceCoupleCount (m : ℕ) : ℕ := Nat.card (SourceCouples m)

/-- Actual source couples satisfy the independently proved code-count bound. -/
theorem sourceCoupleCount_le_codes (m : ℕ) : sourceCoupleCount m ≤ coupleCodeCount m := by
  let _ := finite_coupleCodes m
  exact Nat.card_le_card_of_injective (sourceCoupleCode m) (sourceCoupleCode_injective m)

/-- DH21 Corollary 4.9 and TARGET Proposition 4.4: actual regular couples have exponential count. -/
theorem sourceCoupleCount_le_pow (m : ℕ) : sourceCoupleCount m ≤ (12^9)^m :=
  (sourceCoupleCount_le_codes m).trans (coupleCodeCount_le_pow m)

end WaveTurbulence.Reg
