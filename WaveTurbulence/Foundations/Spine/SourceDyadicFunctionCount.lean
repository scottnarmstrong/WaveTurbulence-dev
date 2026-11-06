/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDyadicLogCount
/-! Finite families of source ladder-scale choices pay only a logarithmic factor per ladder. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine

abbrev SourcePositiveLadderScale (L : ℝ) :=
  {P : ℝ // SourceVine.IsDyadicScale P ∧ L⁻¹ ≤ P ∧ P ≤ 1}

/-- None represents the zero-gap ladder; positive scales use the exact dyadic carrier. -/
abbrev SourceLadderScaleChoice (L : ℝ) := Option (SourcePositiveLadderScale L)

 theorem finite_sourcePositiveLadderScale {L : ℝ} (hL : 0 < L) :
    Finite (SourcePositiveLadderScale L) :=
  (finite_source_dyadic_scales (inv_pos.mpr hL) zero_lt_one).to_subtype

/-- The optional zero scale adds just one to the single-ladder logarithmic cost. -/
theorem card_sourceLadderScaleChoice_le {L : ℝ} (hL : 1 ≤ L) :
    (Nat.card (SourceLadderScaleChoice L) : ℝ) ≤ Real.log L / Real.log 2 + 2 := by
  haveI := finite_sourcePositiveLadderScale (lt_of_lt_of_le zero_lt_one hL)
  letI := Fintype.ofFinite (SourcePositiveLadderScale L)
  change (Nat.card (Option (SourcePositiveLadderScale L)) : ℝ) ≤ _
  rw [Nat.card_eq_fintype_card, Fintype.card_option,
    ← Nat.card_eq_fintype_card, Nat.cast_add, Nat.cast_one]
  have h := card_sourceLadderScales_le hL
  change (Nat.card (SourcePositiveLadderScale L) : ℝ) ≤ _ at h
  linarith

/-- A finite collection of actual ladders has the product scale count used at TARGET L2088. -/
theorem card_sourceLadderScaleFamilies_le {V : Type*} [Finite V] {L : ℝ} (hL : 1 ≤ L) :
    (Nat.card (V → SourceLadderScaleChoice L) : ℝ) ≤
      (Real.log L / Real.log 2 + 2) ^ Nat.card V := by
  rw [Nat.card_fun, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (card_sourceLadderScaleChoice_le hL) _

/-- Critical-atom scales are a subinterval of the positive ladder-scale carrier. -/
theorem card_sourceAtomScales_le {L b : ℝ} (hL : 1 ≤ L) (hb : b ≤ 1) :
    (Nat.card {P : ℝ // SourceVine.IsDyadicScale P ∧ L⁻¹ ≤ P ∧ P ≤ b} : ℝ) ≤
      Real.log L / Real.log 2 + 1 := by
  haveI := finite_sourcePositiveLadderScale (lt_of_lt_of_le zero_lt_one hL)
  let f : {P : ℝ // SourceVine.IsDyadicScale P ∧ L⁻¹ ≤ P ∧ P ≤ b} →
      SourcePositiveLadderScale L := fun P => ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.trans hb⟩
  have hinj : Function.Injective f := by
    intro P Q h
    exact Subtype.ext (congrArg (fun t : SourcePositiveLadderScale L => t.val) h)
  have hc := Nat.card_le_card_of_injective f hinj
  have hc' : (Nat.card {P : ℝ // SourceVine.IsDyadicScale P ∧ L⁻¹ ≤ P ∧ P ≤ b} : ℝ) ≤
      (Nat.card (SourcePositiveLadderScale L) : ℝ) := by exact_mod_cast hc
  exact hc'.trans (card_sourceLadderScales_le hL)

end WaveTurbulence.LGSpine
