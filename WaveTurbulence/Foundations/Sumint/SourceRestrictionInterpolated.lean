/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceRestrictionRecombination
public import WaveTurbulence.Foundations.Sumint.SourceKernelInterpolated
public import WaveTurbulence.Foundations.Sumint.SmallParameterConditions

/-!
# The actual source restriction estimate after common-kernel interpolation

Every analytic input is proved: spatial localization, both endpoints,
interpolation and the full pointwise ambient extension. This theorem
retains the explicit restoration factors for numerical assembly.
-/

public section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.Sumint

/-- TARGET sumint Steps 1--3, before numerical absorption of the explicit restoration costs. -/
theorem exists_source_restriction_interpolated_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : SumintSmallness d γ η)
    (τstar : ℝ) (hτstar : 0 < τstar) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R, ∀ (D : SumintDatum d) (hI : 0 < D.S.I) (A : ℝ),
      1 ≤ A → D.Admissible A L γ η N →
      XNorm00Restr (2*η^8) (sourceOutputTimeSet D) (sourceOutputSet D L γ η)
        (fun t v => D.expr hI L γ δ η t v) ≤
      ENNReal.ofReal ((((9:ℝ)^d*A^d)*summedCellFourierFactor d (30*d)*cellFourierFactor d)^D.S.M)*
        (ENNReal.ofReal (2^(2*η^8))*ENNReal.ofReal ((((D.S.M:ℝ)+1)*parameterMaximum D)^(2*η^8))*
          (ENNReal.ofReal (4^(2*η^8))*
            (ENNReal.ofReal (cellMultiplierRealConstant N*((N:ℝ)+5)*
              (L^(-partitionExponent η))⁻¹*(L^(-partitionExponent η))⁻¹)*
              ENNReal.ofReal (G^D.S.M*δ^(-(D.S.M:ℝ)/2)*
                L^((D.S.M:ℝ)*((d:ℝ)-γ)-
                  (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ))-
                  (1-interpolationWeight η)*(partitionExponent η/20)*(D.M₀:ℝ)+
                  14*(d:ℝ)*interpolationWeight η))))) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_kernel_interpolated_bound d hd γ hγ η hη.eta_pos hη.eta_base
    hη.eta_small hη.gamma_eta hη.sqrt_base τstar hτstar (partitionExponent η)
    (partitionExponent_pos hη.eta_pos) hη.beta_linear hη.beta_pair hη.beta_normal hη.beta_high hη.eight_lt
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D hI A hA hD
  have hLp : 0 < L := by linarith only [hR,hL]
  have hL1 : 1 ≤ L := by linarith only [hR,hL]
  have hh : L^(-partitionExponent η) ∈ Ioc (0:ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hLp _,Real.rpow_le_one_of_one_le_of_nonpos hL1 (by
      linarith only [partitionExponent_pos hη.eta_pos])⟩
  have hθ : 2*η^8 ∈ Icc (0:ℝ) 1 := ⟨by positivity,by linarith only [hη.eight_lt]⟩
  let : Fintype (sourceOutputSet D L γ η) := (finite_sourceOutputSet D hLp γ η).fintype
  apply XNorm00Restr_source_of_kernel_bound (by omega) D hI hA hLp
    (by linarith only [hη.eta_small]) hD hh hθ _ ENNReal.ofReal_lt_top
  intro p ν c
  exact hbound L hL D A hD p ν (sourceOutputSet D L γ η) (fun v => v.1 0-v.1 1)
    (sourceOutputSet_momentum_bounds D hLp γ η) (card_sourceOutputSet_le D hL1 γ η) hI c

end WaveTurbulence.Sumint
