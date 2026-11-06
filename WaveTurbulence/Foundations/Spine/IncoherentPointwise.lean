/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RemainderInputs
public import WaveTurbulence.Foundations.Spine.CouplePointwise
/-! B2.2 consumed on an actual coherent-carrier complement, with input and temporal obligations discharged. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set

theorem norm_incoherent_couple_le (P : WTParams) (hdecay : IncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hC₁ : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    {p n : ℕ} (hp : p < P.D) (R : ℕ → Mom P.d → ℝ) (hR : RemainderBound P R p)
    (hn : n ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (hwf : Q.wf = true) (hsize : Q.size = 2 * n)
    (LG : LayeredGarden 2) (hcan : IsCanonC (p + 1) LG) (hQ : Q.Decodes LG.garden)
    (hincoh : 1 ≤ LG.incoherency Q.links) (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (k : Mom P.d) :
    ‖KQ P.L P.γ P.δ (inputsF P R) LG t k‖ ≤
      P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * LG.incoherency Q.links) := by
  have hinput : ∀ r ≤ p, InputRemainder P (R r) r := fun r hr =>
    InputRemainder_of_RemainderBound P R hd hL hp.le hR hr
  have hlayer : ∀ a, LG.layer a ≤ p := hcan.2.1
  have hX := (hdecay p hp R hinput n hn).1 Q hwf hsize LG hQ hlayer p p
    le_rfl le_rfl (hlayer _) (hlayer _) hincoh
  have hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun m : Fin P.d → ℤ =>
        |inputsF P R (LG.layer ℓ.toNode) (k + latticePoint P.L m)| := fun ℓ _ =>
    summable_inputsF_of_RemainderBound P R hd hL hp.le hR (hlayer _) k
  have hC : 0 ≤ P.C₁ * (P.C₁ * P.δ) ^ n *
      P.L ^ (-(P.gamma1 - Real.sqrt P.η) * LG.incoherency Q.links) :=
    mul_nonneg (mul_nonneg hC₁ (pow_nonneg (mul_nonneg hC₁ hδ) _))
      (Real.rpow_nonneg (by linarith) _)
  exact norm_KQstar_le_of_XNormRestr P.L P.γ P.δ P.η hη (inputsF P R) LG hcan.1.1
    p p t t _ (30 * P.d) (30 * P.d) k ht ht hC hF hX

end WaveTurbulence.LGSpine
