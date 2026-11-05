/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMomentumBridge
public import WaveTurbulence.Foundations.Incoh.CellFourierInversion

/-! # Exact independent-leaf Fourier representation of the localized input -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh WithLp

/-- Inversion is performed separately in each fixed-dimensional actual leaf.
No derivative order grows with the number of leaves. -/
theorem actual_leafCellProduct_eq_frequencyIntegral {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) {d K M : ℕ} {F : Mom d → ℂ} {B : ℝ}
    (hK : d+1 ≤ K) (hB : 0 ≤ B) (hF : Fourier.spatialNorm K M F ≤ ENNReal.ofReal B)
    (c : Fin (2*Q.links.length+1) → Fin d → ℤ) (k : Mom d)
    (x : Fin Q.links.length → Fin 2 → Mom d) :
    (∏ a, leafCell F (c a) ((coupleMomentumData hQ hG).inputMomentum k x a)) =
      ∫ α : Fin (2*Q.links.length+1) → Fin d → ℝ,
        ∏ a, Real.fourierChar (Fourier.timePairing d (α a)
          (ofLp ((coupleMomentumData hQ hG).inputMomentum k x a))) •
          Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F (c a) (toLp 2 y)) (α a) := by
  rw [integral_fintype_prod_volume_eq_prod (fun (a : Fin (2*Q.links.length+1)) (ξ : Fin d → ℝ) =>
    Real.fourierChar (Fourier.timePairing d ξ (ofLp ((coupleMomentumData hQ hG).inputMomentum k x a))) •
      Fourier.timeFourier (fun y : Fin d → ℝ => leafCell F (c a) (toLp 2 y)) ξ)]
  apply Finset.prod_congr rfl
  intro a _
  exact leafCell_eq_fourierIntegral hK hB hF (c a) _

end WaveTurbulence.RegAsymp
