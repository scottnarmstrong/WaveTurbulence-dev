/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Regref.Obligations
public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.B2Bridge

/-!
# B21-SNAP9: the F80 form of the couple obligation implies RA2's `RA1Couple`

`RA1CoupleF80` is copied verbatim from `regref/check/RA1CoupleF80.lean` (the F80 restatement in
`OBLIGATIONS.md`): its remainder norm is the landed `Fourier.mixedRestrictionNorm`, while `RA1Couple` uses B2's
`XNormRestr`. On snapshot 9, `XNormRestr_le_mixedRestrictionNorm` bounds the latter by the former
(`30 * d ≠ 0`), and the factor conjunct is identical.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.B21Snap9

open WaveTurbulence.Regref TTree

/-- The F80 couple obligation (verbatim copy; `regasymp`'s `regular_couple_asymptotics` has exactly this type). -/
def RA1CoupleF80 : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ B : ℝ, ∃ C : ℝ, 1 ≤ C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₁ → ∀ A : ℝ, ∃ L₀ : ℝ,
  ∀ L : ℝ, L₀ ≤ L → ∀ F : Mom d → ℝ, SNormR (40 * d) (40 * d) F ≤ ENNReal.ofReal B →
  ∀ n : ℕ, (n : ℝ) ≤ Real.log L ^ A →
    (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
      (∀ a, LG.layer a = 0) →
      Fourier.mixedRestrictionNorm η (30 * d) (30 * d) (timeBox 0 0) Set.univ
        (fun ts k => KQstar L γ δ (fun _ => F) LG (ts.1 0) (ts.1 1) k.1 - Q.app δ 0 F (ts.1 0) (ts.1 1) k.1) ≤
        ENNReal.ofReal (C * (C * δ) ^ n * L ^ (-(gam1 d γ - Real.sqrt η)))) ∧
    (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
      XNorm00Restr (V := Unit) (1 - η) (timeBox 0 0) Set.univ
          (fun ts _ => (Q.JB 0 (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (C * C ^ n) ∧
        ∀ Z ∈ specialSets Q.links,
          SNormR (30 * d) (30 * d) (Q.Mstar F Z (0, []) (1, [])) ≤ ENNReal.ofReal (C * C ^ n))

/-- The bridge: the F80 couple obligation implies RA2's `RA1Couple`. -/
theorem RA1Couple_of_F80 (h : RA1CoupleF80) : RA1Couple := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη B => ?_⟩
  obtain ⟨C, hC, δ₁, hδ₁, H2⟩ := H η hη B
  refine ⟨C, hC, δ₁, hδ₁, fun δ hδ A => ?_⟩
  obtain ⟨L₀, H3⟩ := H2 δ hδ A
  refine ⟨L₀, fun L hL F hF n hn => ?_⟩
  obtain ⟨h1, h2⟩ := H3 L hL F hF n hn
  refine ⟨fun Q hQ hs LG hdec hl => ?_, h2⟩
  exact (XNormRestr_le_mixedRestrictionNorm' (30 * d) (by omega) η (timeBox 0 0) Set.univ _).trans
    (h1 Q hQ hs LG hdec hl)

end WaveTurbulence.B21Snap9
