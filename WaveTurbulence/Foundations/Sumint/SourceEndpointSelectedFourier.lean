/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceEndpointSelectedSupport
public import WaveTurbulence.Foundations.Sumint.SourceEndpointTracePower
public import WaveTurbulence.Foundations.Sumint.SourceTraceCountingPower

/-!
# Actual selected-coordinate endpoint Fourier L2 bound

The trace estimate is proved from the actual source coefficients. Its
step-dependent counting constant is absorbed into L to 9d. Genuine
integrability and the selected native interval support then give the
Fourier L2 estimate by the established Hausdorff--Young endpoint.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

noncomputable section
local instance {d : ℕ} (D : SumintDatum d) {k : ℕ} (sel : Fin k → D.S.TVar) :
    Fintype {i : D.S.TVar // i ∉ Set.range sel} :=
  @Subtype.fintype D.S.TVar (fun i => i ∉ Set.range sel) (fun _ => Classical.propDecidable _) inferInstance

/-- TARGET sumint Step 3: the actual one- or two-coordinate endpoint marginal has its uniform Fourier L2 bound. -/
theorem exists_source_endpoint_selected_fourier_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (hsqrt : Real.sqrt η ≤ gammaBase γ/8)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) → ∀ (hI : 0 < D.S.I) (c : ℝ) (upper : Bool) (v : D.S.TVar)
      (k : ℕ), k ≤ 2 → ∀ (sel : Fin k → D.S.TVar) (hsel : Function.Injective sel),
      eLpNorm (Fourier.timeFourier (selectedCoordinateMarginal sel hsel
        (sourceExitInput D hI L γ δ η p ν r c (L^(-β)) upper v))) 2 ≤
        ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) := by
  obtain ⟨G,hG,htrace⟩ := exists_source_endpoint_trace_power_bound d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨RT,hRT,htrace⟩ := htrace δ N hδ hτ
  obtain ⟨RC,hRC,hcount⟩ := exists_sourceTraceCountingCost_le_power d N (by omega) η
  refine ⟨max RT RC,hRT.trans (le_max_left _ _),?_⟩
  intro L hL D A hD p ν r hr hrupper hI c upper v k hk sel hsel
  have hLT : RT ≤ L := (le_max_left _ _).trans hL
  have hLC : RC ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := by linarith only [hRT,hLT]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hh : L^(-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (neg_nonpos.mpr hβ.le)
  let F := sourceExitInput D hI L γ δ η p ν r c (L^(-β)) upper v
  let B := L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ
  have hB : 0 ≤ B := by
    dsimp [B,sourcePositiveMassBudget]
    exact mul_nonneg (Real.rpow_nonneg hLp.le _) (mul_nonneg
      (mul_nonneg (pow_nonneg (zero_le_one.trans hG) _) (Real.rpow_nonneg hδ.1.le _)) (Real.rpow_nonneg hLp.le _))
  have ht (x : Fin k → ℝ) :
      (∫⁻ y : {i : D.S.TVar // i ∉ Set.range sel} → ℝ, ‖F ((selectedCoordinateSplit sel hsel).symm (x,y))‖ₑ) ≤
        ENNReal.ofReal B := by
    have he := htrace L hLT D A hD p ν r hr hrupper hI c upper v k hk sel hsel x
    apply he.trans
    calc
      _ ≤ ENNReal.ofReal (L^(9*(d:ℝ)))*ENNReal.ofReal (sourcePositiveMassBudget D G L γ δ) :=
        mul_le_mul' (hcount L hLC) le_rfl
      _ = _ := (ENNReal.ofReal_mul (Real.rpow_nonneg hLp.le _)).symm
  have hb := selectedMarginal_fourier_L2_le_of_mass sel hsel F
    (measurable_sourceExitInput D hI hLp γ δ η p ν r c (L^(-β)) upper v)
    (integrable_sourceExitInput D hI hLp γ δ η (by linarith only [hηsmall]) p ν r c (L^(-β)) upper v)
    (fun j => enlargedTimeLower D c (L^(-β)) (sel j))
    (fun j => enlargedTimeUpper D c (L^(-β)) (sel j))
    (volume_selected_source_box_le_nine D c hh hk sel) hB (fun x => by
      convert ht x using 1
      congr 3
      exact Subsingleton.elim _ _)
    (sourceExitInput_eq_zero_of_selected_outside D hI L γ δ η p ν r c (L^(-β)) upper v sel)
  simpa only [B,mul_assoc] using hb

end
end WaveTurbulence.Sumint
