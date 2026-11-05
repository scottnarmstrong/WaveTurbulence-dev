/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.LeadingGeometricBudget

/-! # Geometric full spatial bound on the original source singular leaf kernel -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Incoh Links ApproxNT

/-- DH23 Prop6.1 spatial-factor analytic estimate before its recursive
Mstar identification. The literal source singular kernel has a geometric
bound at full30d derivative/weight order, with constants before every
order cutoff. This does not substitute for the recursive Mstar conclusion. -/
theorem actual_source_singular_spatial_bound {d : ℕ} (hd : 3 ≤ d) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (G : Garden 2) (Q : RegCpl) (hQ : Q.Decodes G) (hG : IsCouple G),
      0 < Q.links.length → ∀ F : Mom d → ℂ,
      Fourier.spatialNorm (40*d) (40*d) F ≤ ENNReal.ofReal B →
      ∀ J : Finset (Fin Q.links.length),
      Fourier.spatialNorm (30*d) (30*d) (fun k => singInt J (fun x y =>
        ∏ a, F ((coupleMomentumData hQ hG).inputMomentum k
          (fun j i => if i=0 then x j else y j) a))) ≤
        ENNReal.ofReal (C*C^Q.links.length) := by
  obtain ⟨Ccover,hCc,Mcell,hMc,hsp⟩ := actual_source_singInt_spatialNorm hd
  let P := leafWeightedMomentLocalizationConstant d (30*d+1) (40*d) (30*d)*B
  have hP : 0 ≤ P := by
    unfold P leafWeightedMomentLocalizationConstant
    exact mul_nonneg (mul_nonneg (leafCellFourierMomentConstant_nonneg _ _ _)
      (tsum_nonneg (cellCenterWeight_nonneg _))) hB
  let a := maskedSourceSpatialConstant d 1 (30*d) (30*d)*(1+2*Real.pi)*P
  let b := ((2+Real.sqrt d)^(2*(30*d)))*((2*max 1 (Real.sqrt d)+5)^(2*d))*Mcell*
    (halfLinkFirstMomentConstant d)^2*(9*(1+4*Real.pi))*Ccover*P^2
  obtain ⟨C,hC,hgeom⟩ := exists_common_geometric_bound a b
  refine ⟨C,hC,?_⟩
  intro G Q hQ hG hn F hF J
  have hh := hsp G Q hQ hG hn (30*d) (30*d) (40*d) (40*d)
    (by omega) (by omega) B hB F hF J
  have hbudget := leading_spatial_budget_le_geometric (d := d) (N := 30*d) (W := 30*d) (M := 40*d)
    Q (zero_le_one.trans hMc) hCc.le hB
  apply hh.trans
  have hmask : 0 ≤ maskedSourceSpatialConstant d (2*Q.links.length+1) (30*d) (30*d) := by
    unfold maskedSourceSpatialConstant
    have hr := zero_le_one.trans (one_le_rootMaskDerivativeConstant d (30*d))
    positivity
  have hhalf := (halfLinkFirstMomentConstant_pos d).le
  have hrow := (spectralFrequencyLoss_pos Q).le
  have hcoef : 0 ≤ maskedSourceSpatialConstant d (2*Q.links.length+1) (30*d) (30*d)*
      ((1+2*Real.pi)*
        ((((2*max 1 (Real.sqrt d)+5)^(2*d))^Q.links.length*Mcell^Q.links.length*
          halfLinkFirstMomentConstant d^(2*Q.links.length))*spectralFrequencyLoss Q)) := by
    have hm := zero_le_one.trans hMc
    positivity
  rw [← ENNReal.ofReal_pow hP,← ENNReal.ofReal_mul (pow_nonneg hCc.le _),
    ← ENNReal.ofReal_mul hcoef]
  apply ENNReal.ofReal_le_ofReal
  exact hbudget.trans (hgeom Q.links.length)

end WaveTurbulence.RegAsymp
