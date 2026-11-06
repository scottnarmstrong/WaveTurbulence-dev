/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.NonregularNumericsP
public import WaveTurbulence.Foundations.Spine.TwistClosedNR
public import WaveTurbulence.Foundations.Spine.LayergardenAssembly
/-! `NonregularEstimateAt P` (TARGET terms (a),(b)) from the Stage 1 gate (design P*: pair-type evaluations,
twist-closed carriers), the molecular source gates, and the explicit numerical data for each stage `p < D`
(`GardenNum`, `CoupleNum`). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical ENNReal

theorem nonregular_of_data (C₀ : ℕ) (P : WTParams) (hs : PieceSmall P)
    (hcoarse : CoarseSplicedAt P) (hfourier : LadderFourierAt P) (hcount : FinalCountAt P)
    (habs : FinalAbsorptionAt (6 * C₀) P) (hlog : 1 ≤ Real.log P.L) (hgate : Stage1ReductionAt C₀ P)
    (hd : 1 ≤ P.d) (hlowP : LowProfileAt P) (htime : P.τstar = (P.D : ℝ) * P.δ)
    {Cφ : ℝ} (hCφ : 0 ≤ Cφ)
    (hφ : ∀ τ ∈ Icc (0 : ℝ) P.τstar,
      SNormR (P.Lambda 0) (P.Lambda 0) (P.φ τ) ≤ ENNReal.ofReal Cφ)
    (hR1 : ∀ p, 1 ≤ P.R (p + 1))
    (hG : ∀ p, p < P.D → GardenNum P Cφ p) (hC : ∀ p, p < P.D → CoupleNum P Cφ p) :
    NonregularEstimateAt P := by
  intro p hp Rr hRr N hN t ht
  refine ⟨?_, ?_⟩
  · intro m hm2 hmmax ζ hζ n
    exact garden_estimate_of_gate C₀ P hs hcoarse hfourier hcount habs hlog hgate hd hlowP htime hCφ hφ
      hp Rr hRr hm2 hmmax ζ hζ n hN ht (twistClosed_gardenSet P hd hp hm2 ζ hN) (hG p hp m N hm2 hmmax hN)
  · exact couple_estimate_of_gate C₀ P hs hcoarse hfourier hcount habs hlog hgate hd hlowP htime hCφ hφ
      hp Rr hRr (hR1 p) hN ht (twistClosed_coupleSet P hd hp hN) (hC p hp N hN)

end WaveTurbulence.LGSpine
