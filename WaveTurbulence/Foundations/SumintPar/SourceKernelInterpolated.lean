/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceKernelPositiveBound
public import WaveTurbulence.Foundations.SumintPar.SourceKernelNegativeBound
public import WaveTurbulence.Foundations.SumintPar.EndpointInterpolationPowers

/-!
# The same actual source kernel interpolated to the drafted time regularity

The positive and negative estimates apply to precisely the same explicit
ambient kernel and finite output family. Only the positive endpoint pays
the 14d loss. Its interpolation fraction is kept explicit, as is the
negative endpoint discrepancy gain. Constants are chosen before delta.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- TARGET sumint Step 3: the actual common kernel interpolates to exactly 2 eta^8. -/
theorem exists_source_kernel_interpolated_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (hsqrt : Real.sqrt η ≤ gammaBase γ/8)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) (hsmall : 8*η^8 < 1) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d),
      ∀ (V : Type*) [Fintype V] (r : V → Mom d), (∀ v, 1/L ≤ ‖r v‖ ∧ ‖r v‖ ≤ L^(-γ+η)) →
      (Fintype.card V:ℝ) ≤ (3*L)^(4*d) → ∀ (hI : 0 < D.S.I) (c : ℝ),
      XNorm00 (2*η^8) (fun z v => kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p ν (r v)) z) ≤
        ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
          L^((D.S.M:ℝ)*((d:ℝ)-γ)-
            (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
            (1-interpolationWeight η)*(β/20)*(D.M₀:ℝ)+14*(d:ℝ)*interpolationWeight η)) := by
  obtain ⟨GP,hGP,hP⟩ := exists_source_kernel_positive_bound d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  obtain ⟨GN,hGN,hN⟩ := exists_source_kernel_negative_bound d hd hγ hη hηbase hηsmall hsqrt hγη
    τstar hτstar β hβ hβγ hβη hβnormal hhigh (η^8) (by positivity)
  let J := max GP GN
  let C := negativeEndpointCoefficient (η^8)
  let G := max 1 C*J
  have hJ : 1 ≤ J := hGP.trans (le_max_left _ _)
  have hG : 1 ≤ G := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hJ
  have hJG : J ≤ G := le_mul_of_one_le_left (zero_le_one.trans hJ) (le_max_left _ _)
  have hPG : GP ≤ G := (le_max_left _ _).trans hJG
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨RP,hRP,hP⟩ := hP δ N hδ hτ
  obtain ⟨RN,hRN,hN⟩ := hN δ N hδ hτ
  refine ⟨max RP RN,hRP.trans (le_max_left _ _),?_⟩
  intro L hL D A hD p ν V _ r hr hcard hI c
  have hLP : RP ≤ L := (le_max_left _ _).trans hL
  have hLN : RN ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith only [hRP,hLP]
  have hM : 0 < D.S.M := size_pos D.S hI
  let E := (D.S.M:ℝ)*((d:ℝ)-γ)-
    (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))
  let B := G^D.S.M*δ^(-(D.S.M:ℝ)/2)
  let F := fun z v => kernelExtension D hI c (L^(-β)) (weightedCutoffInput D L γ δ η p ν (r v)) z
  have hB : 0 < B := mul_pos (pow_pos (zero_lt_one.trans_le hG) _) (Real.rpow_pos_of_pos hδ.1 _)
  have hp : XNorm00 ((1:ℝ)/4) F ≤ ENNReal.ofReal (B*L^(E+14*(d:ℝ))) := by
    apply (hP L hLP D A hD p ν V r hr hcard hI c).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hGP) hPG _) (Real.rpow_nonneg hδ.1.le _))
      (Real.rpow_nonneg hLp.le _)
  have hn : XNorm00 (-η^8) F ≤ ENNReal.ofReal (B*L^(E-(β/20)*(D.M₀:ℝ))) := by
    apply (hN L hLN D A hD hI p ν V r hr c).trans
    apply ENNReal.ofReal_le_ofReal
    have hc := coefficient_mul_pow_le_common (C := C) (H := J) (zero_le_one.trans hGN) (le_max_right _ _) hM
    calc
      _ = (C*GN^D.S.M)*δ^(-(D.S.M:ℝ)/2)*L^(E-(β/20)*(D.M₀:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hδ.1.le _)) (Real.rpow_nonneg hLp.le _)
  have ha := interpolationWeight_bounds hη.le hsmall.le
  calc
    _ ≤ XNorm00 ((1:ℝ)/4) F^(interpolationWeight η)*XNorm00 (-η^8) F^(1-interpolationWeight η) :=
      XNorm00_target_interpolate hη hsmall F
    _ ≤ (ENNReal.ofReal (B*L^(E+14*(d:ℝ))))^(interpolationWeight η)*
        (ENNReal.ofReal (B*L^(E-(β/20)*(D.M₀:ℝ))))^(1-interpolationWeight η) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hp ha.1) (ENNReal.rpow_le_rpow hn (sub_nonneg.mpr ha.2.1))
    _ = _ := by
      rw [geometric_endpoint_budget hB hLp]
      congr 2
      congr 1
      dsimp only [E]
      ring

end WaveTurbulence.SumintPar
