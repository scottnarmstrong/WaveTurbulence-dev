/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceKernelInterpolated
public import WaveTurbulence.Foundations.SumintPar.SourceFiniteKernelPositive

/-! # V5W-T T1: the source kernel bound with an output-dependent input modulation

`exists_source_kernel_interpolated_boundOut` is main's `SumintPar.exists_source_kernel_interpolated_bound` with the
input modulation `ν v` depending on the output `v` (supplement Lemma 4.2: the top filter of Lemma 9.3 has input
frequency `∝ r(E)/S`).  Both endpoints of main's proof already bound each output separately (positive endpoint:
`XNorm00_le_sum_scalar` and a per-output scalar bound; negative endpoint: a per-output time mass into
`kernelExtension_negative_norm_le`), so the copies replace `ν` by `ν v` at those call sites only.

Copied by source from main 416902c8 (`SumintPar/SourceFiniteKernelPositive.lean`, `SourceKernelPositiveBound.lean`,
`SourceKernelNegativeBound.lean`, `SourceKernelInterpolated.lean`; sha256 in `COPIED-SHA256SUMS`).  Edits: suffix `Out`,
`ν : V → D.S.VIdx → Mom d` bound after `V`, `ν` ↦ `ν v` in the per-output calls.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Flower.V5WT
open WaveTurbulence WaveTurbulence.SumintPar

/-- Output-dependent copy of `exists_source_finite_kernel_positive_bound`. -/
theorem exists_source_finite_kernel_positive_boundOut (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (hsqrt : Real.sqrt η ≤ gammaBase γ/8)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintPar.SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ),
      ∀ (V : Type*) [Fintype V] (ν : V → D.S.VIdx → Mom d) (r : V → Mom d),
      (∀ v, 1/L ≤ ‖r v‖ ∧ ‖r v‖ ≤ L^(-γ+η)) →
      ∀ (hI : 0 < D.S.I) (c : ℝ),
      XNorm00 ((1:ℝ)/4) (fun z v => kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p (ν v) (r v)) z) ≤
        sourceExitKernelConstant*ENNReal.ofReal (2*(D.S.M:ℝ)*(Fintype.card V:ℝ))*
          ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_scalar_kernel_positive_bound d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p V _ ν r hr hI c
  have hLp : 0 < L := by linarith only [hR,hL]
  have hηthird : η ≤ 1/3 := by linarith only [hηsmall]
  have hFi (v : V) : Integrable (kernelExtension D hI c (L^(-β))
      (weightedCutoffInput D L γ δ η p (ν v) (r v))) :=
    integrable_kernelExtension D hI c (L^(-β)) _ (measurable_weightedCutoffInput D hLp γ δ η p (ν v) (r v))
      (integrableOn_weightedCutoffInput D hLp γ δ η hηthird p (ν v) (r v) c (L^(-β)))
  calc
    _ ≤ ∑ v : V, Fourier.timeFourierNorm ((1:ℝ)/4) (kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p (ν v) (r v))) :=
      XNorm00_le_sum_scalar ((1:ℝ)/4) _ hFi
    _ ≤ ∑ _v : V, sourceExitKernelConstant*ENNReal.ofReal (2*(D.S.M:ℝ))*
        ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) :=
      Finset.sum_le_sum (fun v _ => hbound L hL D A hD p (ν v) (r v) (hr v).1 (hr v).2 hI c)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(D.S.M:ℝ)),ENNReal.ofReal_natCast]
      ring

/-- Output-dependent copy of `exists_source_kernel_positive_bound`. -/
theorem exists_source_kernel_positive_boundOut (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (hsqrt : Real.sqrt η ≤ gammaBase γ/8)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintPar.SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ),
      ∀ (V : Type*) [Fintype V] (ν : V → D.S.VIdx → Mom d) (r : V → Mom d),
      (∀ v, 1/L ≤ ‖r v‖ ∧ ‖r v‖ ≤ L^(-γ+η)) →
      (Fintype.card V:ℝ) ≤ (3*L)^(4*d) → ∀ (hI : 0 < D.S.I) (c : ℝ),
      XNorm00 ((1:ℝ)/4) (fun z v => kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p (ν v) (r v)) z) ≤
        ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
          L^((D.S.M:ℝ)*((d:ℝ)-γ)-
            (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))+14*(d:ℝ))) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_finite_kernel_positive_boundOut d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  let C := sourceExitKernelRealConstant
  let H := 12*C*3^(4*d)*G
  have hC : 1 ≤ C := le_max_left _ _
  have hCn : 0 ≤ C := zero_le_one.trans hC
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hC)
      (one_le_pow₀ (by norm_num))) hG
  refine ⟨H,hH,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p V _ ν r hr hcard hI c
  have hL1 : 1 ≤ L := by linarith only [hR,hL]
  have hM : 0 < D.S.M := size_pos D.S hI
  have hcost : 0 ≤ 2*(D.S.M:ℝ)*(Fintype.card V:ℝ) := by positivity
  calc
    _ ≤ sourceExitKernelConstant*ENNReal.ofReal (2*(D.S.M:ℝ)*(Fintype.card V:ℝ))*
        ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) :=
      hbound L hL D A hD p V ν r hr hI c
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (2*(D.S.M:ℝ)*(Fintype.card V:ℝ))*
        ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) :=
      mul_le_mul' (mul_le_mul' sourceExitKernelConstant_le_ofReal le_rfl) le_rfl
    _ = ENNReal.ofReal (C*(2*(D.S.M:ℝ)*(Fintype.card V:ℝ))*
        (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ)) := by
      rw [← ENNReal.ofReal_mul hCn,← ENNReal.ofReal_mul (mul_nonneg hCn hcost)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (finite_positive_endpoint_cost_le hC hG hL1 hδ.1 hM hcard)

/-- Output-dependent copy of `exists_source_kernel_negative_bound`. -/
theorem exists_source_kernel_negative_boundOut (d : ℕ) (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Ioo (0:ℝ) 1) (hη : 0 < η) (hηbase : η ≤ gammaBase γ) (hηsmall : η ≤ 1/24)
    (hs : Real.sqrt η ≤ gammaBase γ/8) (hγη : γ+η ≤ 1)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β)
    (hβpair : β/2 < 2*γ) (hβweyl : β/2 < 2*((d:ℝ)-1)*(1-γ)-η)
    (hβnormal : β < 20*γ) (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintPar.SumintDatum d) (A : ℝ), D.Admissible A L γ η N → ∀ hI : 0 < D.S.I,
      ∀ (p : D.S.VIdx → Fin d → ℝ),
      ∀ (V : Type*) (ν : V → D.S.VIdx → Mom d) (r : V → Mom d),
      (∀ v, 1/L ≤ ‖r v‖ ∧ ‖r v‖ ≤ L^(-γ+η)) → ∀ c : ℝ,
      XNorm00 (-ε) (fun z v => kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p (ν v) (r v)) z) ≤
      ENNReal.ofReal (negativeEndpointCoefficient ε*(G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
        L^((D.S.M:ℝ)*((d:ℝ)-γ)-
          (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
          (β/20)*(D.M₀:ℝ)))) := by
  obtain ⟨G,hG,hsource⟩ := exists_source_static_power_bound d hd hγ hη hηbase hηsmall hs hγη
    τstar hτstar β hβ hβpair hβweyl hβnormal hhigh
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hsource δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD hI p V ν r hr c
  have hLp : 0 < L := by linarith [hR.trans hL]
  let B := G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
    L^((D.S.M:ℝ)*((d:ℝ)-γ)-
      (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
      (β/20)*(D.M₀:ℝ))
  have hGn : 0 ≤ G := zero_le_one.trans hG
  have hδp : 0 < δ := hδ.1
  have hBn : 0 ≤ B := by dsimp [B]; positivity
  have hηthird : η ≤ 1/3 := by linarith only [hηsmall]
  have hi (v : V) := integrableOn_weightedCutoffInput D hLp γ δ η hηthird p (ν v) (r v) c (L^(-β))
  have hmass (v : V) : (∫ u in localInputTimeDomain D c (L^(-β)),
      ‖weightedCutoffInput D L γ δ η p (ν v) (r v) u‖) ≤ B := by
    apply (ENNReal.ofReal_le_ofReal_iff hBn).mp
    have he := ofReal_integral_eq_lintegral_ofReal (hi v).norm (ae_of_all _ (fun u => norm_nonneg
      (weightedCutoffInput D L γ δ η p (ν v) (r v) u)))
    simp_rw [ofReal_norm] at he
    rw [he,lintegral_enorm_weightedCutoffInput D hLp]
    have hb := hbound L hL D A hD p (ν v) (r v) (hr v).1 (hr v).2 0 c
    rw [← enlargedInputTimeBox_eq_Icc] at hb
    exact hb
  have hb := kernelExtension_negative_norm_le D hI c (L^(-β))
    (fun u v => weightedCutoffInput D L γ δ η p (ν v) (r v) u)
    (fun v => measurable_weightedCutoffInput D hLp γ δ η p (ν v) (r v)) hi hBn hmass hε
  exact hb.trans_eq (by congr 1; unfold negativeEndpointCoefficient; ring)

/-- **T1.** Output-dependent copy of `exists_source_kernel_interpolated_bound`: the common kernel with input
modulation `ν v` at the output `v` interpolates to `2 η⁸` with the same constants. -/
theorem exists_source_kernel_interpolated_boundOut (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (hsqrt : Real.sqrt η ≤ gammaBase γ/8)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) (hsmall : 8*η^8 < 1) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintPar.SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ),
      ∀ (V : Type*) [Fintype V] (ν : V → D.S.VIdx → Mom d) (r : V → Mom d),
      (∀ v, 1/L ≤ ‖r v‖ ∧ ‖r v‖ ≤ L^(-γ+η)) →
      (Fintype.card V:ℝ) ≤ (3*L)^(4*d) → ∀ (hI : 0 < D.S.I) (c : ℝ),
      XNorm00 (2*η^8) (fun z v => kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p (ν v) (r v)) z) ≤
        ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
          L^((D.S.M:ℝ)*((d:ℝ)-γ)-
            (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
            (1-interpolationWeight η)*(β/20)*(D.M₀:ℝ)+14*(d:ℝ)*interpolationWeight η)) := by
  obtain ⟨GP,hGP,hP⟩ := exists_source_kernel_positive_boundOut d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  obtain ⟨GN,hGN,hN⟩ := exists_source_kernel_negative_boundOut d hd hγ hη hηbase hηsmall hsqrt hγη
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
  intro L hL D A hD p V _ ν r hr hcard hI c
  have hLP : RP ≤ L := (le_max_left _ _).trans hL
  have hLN : RN ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith only [hRP,hLP]
  have hM : 0 < D.S.M := size_pos D.S hI
  let E := (D.S.M:ℝ)*((d:ℝ)-γ)-
    (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))
  let B := G^D.S.M*δ^(-(D.S.M:ℝ)/2)
  let F := fun z v => kernelExtension D hI c (L^(-β)) (weightedCutoffInput D L γ δ η p (ν v) (r v)) z
  have hB : 0 < B := mul_pos (pow_pos (zero_lt_one.trans_le hG) _) (Real.rpow_pos_of_pos hδ.1 _)
  have hp : XNorm00 ((1:ℝ)/4) F ≤ ENNReal.ofReal (B*L^(E+14*(d:ℝ))) := by
    apply (hP L hLP D A hD p V ν r hr hcard hI c).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hGP) hPG _) (Real.rpow_nonneg hδ.1.le _))
      (Real.rpow_nonneg hLp.le _)
  have hn : XNorm00 (-η^8) F ≤ ENNReal.ofReal (B*L^(E-(β/20)*(D.M₀:ℝ))) := by
    apply (hN L hLN D A hD hI p V ν r hr c).trans
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

end WaveTurbulence.Flower.V5WT
