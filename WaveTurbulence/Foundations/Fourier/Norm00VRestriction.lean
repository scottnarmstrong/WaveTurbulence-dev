/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.Norm00V

/-!
# Restriction and reindexing for general-variable order-zero mixed norms

TARGET L589. Restriction means agreement at every point. The equivalent
ambient-function formulation is the one used in the Wave B norm drafts.
-/

public section

namespace WaveTurbulence.Fourier
open Set
open scoped ENNReal

/-- Any pointwise agreeing extension bounds the restriction norm. -/
theorem mixedRestrictionNorm00_le_extension {r : ℕ} {V : Type*} {θ : ℝ}
    {B : Set (Fin r → ℝ)} {K : Set V} {F : B → K → ℂ}
    (G : (Fin r → ℝ) → V → ℂ) (hG : ∀ (t : B) (v : K), G t v = F t v) :
    mixedRestrictionNorm00 θ B K F ≤ mixedFourierNorm00 θ G :=
  iInf_le_of_le G (iInf_le_of_le hG le_rfl)

/-- Restricting an ambient function can only decrease its norm. -/
theorem mixedRestrictionNorm00_le {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) (F : (Fin r → ℝ) → V → ℂ) :
    mixedRestrictionNorm00 θ B K (fun t v => F t v) ≤ mixedFourierNorm00 θ F :=
  mixedRestrictionNorm00_le_extension F (fun _ _ => rfl)

@[simp] theorem mixedRestrictionNorm00_zero {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) : mixedRestrictionNorm00 θ B K (fun _ _ => 0) = 0 := by
  apply le_antisymm _ bot_le
  exact (mixedRestrictionNorm00_le θ B K (fun _ _ => 0)).trans (by simp)

/-- Subtype-domain restrictions and ambient agreement conditions give the same infimum. -/
theorem mixedRestrictionNorm00_eq_agreement {r : ℕ} {V : Type*} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set V) (F : (Fin r → ℝ) → V → ℂ) :
    mixedRestrictionNorm00 θ B K (fun t v => F t v) =
      ⨅ (G : (Fin r → ℝ) → V → ℂ) (_ : ∀ t ∈ B, ∀ v ∈ K, G t v = F t v), mixedFourierNorm00 θ G := by
  unfold mixedRestrictionNorm00
  apply iInf_congr
  intro G
  have he : (∀ (t : B) (v : K), G t v = F t v) ↔ (∀ t ∈ B, ∀ v ∈ K, G t v = F t v) :=
    ⟨fun h t ht v hv => h ⟨t, ht⟩ ⟨v, hv⟩, fun h t v => h t t.property v v.property⟩
  rw [he]

/-- Restricting the time and vector domains decreases the extension infimum. -/
theorem mixedRestrictionNorm00_mono {r : ℕ} {V : Type*} (θ : ℝ)
    {B B' : Set (Fin r → ℝ)} {K K' : Set V} (hB : B ⊆ B') (hK : K ⊆ K')
    (F : B' → K' → ℂ) :
    mixedRestrictionNorm00 θ B K (fun t v => F ⟨t, hB t.property⟩ ⟨v, hK v.property⟩) ≤
      mixedRestrictionNorm00 θ B' K' F := by
  apply le_iInf
  intro G
  apply le_iInf
  intro hG
  exact mixedRestrictionNorm00_le_extension G (fun t v => hG ⟨t, hB t.property⟩ ⟨v, hK v.property⟩)

/-- Changing the vector-variable type by a bijection leaves the unrestricted norm unchanged. -/
theorem mixedFourierNorm00_equiv {r : ℕ} {V W : Type*} (θ : ℝ) (e : V ≃ W)
    (F : (Fin r → ℝ) → W → ℂ) :
    mixedFourierNorm00 θ (fun t v => F t (e v)) = mixedFourierNorm00 θ F := by
  have he : (∀ v, MeasureTheory.Integrable (fun t => F t (e v))) ↔
      (∀ w, MeasureTheory.Integrable (fun t => F t w)) :=
    ⟨fun h w => by simpa only [e.apply_symm_apply] using h (e.symm w), fun h v => h (e v)⟩
  unfold mixedFourierNorm00
  rw [he]
  split_ifs
  · apply MeasureTheory.lintegral_congr
    intro ξ
    congr 1
    exact e.iSup_comp (g := fun w => ‖timeFourier (fun t => F t w) ξ‖ₑ)
  · rfl

/-- On momentum space, the restricted norm is the landed mixed restriction at orders zero. -/
theorem mixedRestrictionNorm00_eq_mixedRestrictionNorm {r d : ℕ} (θ : ℝ)
    (B : Set (Fin r → ℝ)) (K : Set (Mom d)) (F : B → K → ℂ) :
    mixedRestrictionNorm00 θ B K F = mixedRestrictionNorm θ 0 0 B K F := by
  unfold mixedRestrictionNorm00 mixedRestrictionNorm
  simp only [mixedFourierNorm00_eq_mixedFourierNorm]

end WaveTurbulence.Fourier
