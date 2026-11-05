/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LatticeCoordinates

/-! # DH23 (newsum1): exact reindexing of the actual couple kernel

This step retains the original time integral and the exact squared Wick
factor. Localization and NT approximation occur after this identity.
-/

public section
namespace WaveTurbulence.RegAsymp
open Links

/-- Reindex KQstar by the proved integer-decoration equivalence. There is
no assumed expansion or assumed change-of-variables formula. -/
theorem KQstar_integerLinkEquiv {d : ℕ} (L γ δ : ℝ) (F : Mom d → ℝ)
    (LG : LayeredGarden 2) {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    (hG : IsCouple LG.garden) (t s : ℝ) (k : Mom d) :
    KQstar L γ δ (fun _ => F) LG t s k =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
      ∑' θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ),
        let κ := ((integerLinkEquiv hQ hG d).symm θ).val
        ((∏ j, epsXY (θ j).1 (θ j).2 ^ 2 : ℝ) : ℂ) *
          phaseIntegral L γ δ LG.garden
            (kDomain LG (fun b => if b.1.1 = 0 then t else s) 0) 0
            (cosetDecoration LG.garden L k κ) *
          ∏ ℓ ∈ inputLeaves LG.garden, (F (cosetDecoration LG.garden L k κ ℓ.toNode) : ℂ) := by
  unfold KQstar kernelK
  congr 1
  rw [tsum_integerLinkEquiv hQ hG d]
  apply tsum_congr
  intro θ
  rw [epsDec_integerLinkEquiv_symm hQ hG d θ]

end WaveTurbulence.RegAsymp
