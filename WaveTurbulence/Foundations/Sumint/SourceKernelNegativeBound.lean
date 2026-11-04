/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceStaticPowerBound
public import WaveTurbulence.Foundations.Sumint.WeightedCutoffInput
public import WaveTurbulence.Foundations.Sumint.KernelExtensionNegativeNorm

/-!
# The actual weighted source kernel satisfies the negative Fourier endpoint

The input mass is supplied by the actual Step 2 estimate, uniformly over
an arbitrary output carrier. The supremum stays inside the Fourier
integral; no output-cardinality factor is paid. Native input and ambient
output time integrability are supplied by the explicit kernel construction.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- The explicit three-time negative endpoint coefficient (finite for epsilon positive). -/
@[expose] noncomputable def negativeEndpointCoefficient (ε : ℝ) : ℝ :=
  2*∫ ξ : Fin 3 → ℝ, Fourier.timeBracket ξ^(-ε)*∏ j, 1/scalarBracket (ξ j)

/-- TARGET sumint Step 3: the actual weighted cutoff kernel has the negative Fourier endpoint bound. -/
theorem exists_source_kernel_negative_bound (d : ℕ) (hd : 3 ≤ d) {γ η : ℝ}
    (hγ : γ ∈ Ioo (0:ℝ) 1) (hη : 0 < η) (hηbase : η ≤ gammaBase γ) (hηsmall : η ≤ 1/24)
    (hs : Real.sqrt η ≤ gammaBase γ/8) (hγη : γ+η ≤ 1)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β)
    (hβpair : β/2 < 2*γ) (hβweyl : β/2 < 2*((d:ℝ)-1)*(1-γ)-η)
    (hβnormal : β < 20*γ) (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N → ∀ hI : 0 < D.S.I,
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d),
      ∀ (V : Type*) (r : V → Mom d), (∀ v, 1/L ≤ ‖r v‖ ∧ ‖r v‖ ≤ L^(-γ+η)) → ∀ c : ℝ,
      XNorm00 (-ε) (fun z v => kernelExtension D hI c (L^(-β))
        (weightedCutoffInput D L γ δ η p ν (r v)) z) ≤
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
  intro L hL D A hD hI p ν V r hr c
  have hLp : 0 < L := by linarith [hR.trans hL]
  let B := G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
    L^((D.S.M:ℝ)*((d:ℝ)-γ)-
      (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
      (β/20)*(D.M₀:ℝ))
  have hGn : 0 ≤ G := zero_le_one.trans hG
  have hδp : 0 < δ := hδ.1
  have hBn : 0 ≤ B := by dsimp [B]; positivity
  have hηthird : η ≤ 1/3 := by linarith only [hηsmall]
  have hi (v : V) := integrableOn_weightedCutoffInput D hLp γ δ η hηthird p ν (r v) c (L^(-β))
  have hmass (v : V) : (∫ u in localInputTimeDomain D c (L^(-β)),
      ‖weightedCutoffInput D L γ δ η p ν (r v) u‖) ≤ B := by
    apply (ENNReal.ofReal_le_ofReal_iff hBn).mp
    have he := ofReal_integral_eq_lintegral_ofReal (hi v).norm (ae_of_all _ (fun u => norm_nonneg
      (weightedCutoffInput D L γ δ η p ν (r v) u)))
    simp_rw [ofReal_norm] at he
    rw [he,lintegral_enorm_weightedCutoffInput D hLp]
    have hb := hbound L hL D A hD p ν (r v) (hr v).1 (hr v).2 0 c
    rw [← enlargedInputTimeBox_eq_Icc] at hb
    exact hb
  have hb := kernelExtension_negative_norm_le D hI c (L^(-β))
    (fun u v => weightedCutoffInput D L γ δ η p ν (r v) u)
    (fun v => measurable_weightedCutoffInput D hLp γ δ η p ν (r v)) hi hBn hmass hε
  exact hb.trans_eq (by congr 1; unfold negativeEndpointCoefficient; ring)

end WaveTurbulence.Sumint
