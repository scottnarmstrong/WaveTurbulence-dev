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

end WaveTurbulence.Fourier
