/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceAllCoreBudgets
public import WaveTurbulence.Foundations.Sumint.CoreBudgetRecombination
public import WaveTurbulence.Foundations.Sumint.MixedCoreProductBudget

/-!
# Actual fixed/free source core product with the retained weight gain

The full mass estimates are constructed from the original source bounds,
not assumed. Two fixed native times cost at most eight inputs. The
remaining core budgets collect with the original bad and M1 gains.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The global source mass power needed at the positive Fourier endpoint, without an M0 gain. -/
@[expose] noncomputable def sourcePositiveMassBudget {d : ℕ} (D : SumintDatum d) (G L γ δ : ℝ) : ℝ :=
  G^D.S.M*δ^(-(D.S.M:ℝ)/2)*L^((D.S.M:ℝ)*((d:ℝ)-γ)-
    (gammaBase γ/8)*(((Finset.univ.filter (fun i => D.S.nor i = false)).card:ℝ)+(D.M₁:ℝ)))

/-- The explicit total counting and time-volume cost for at most eight touched inputs. -/
@[expose] noncomputable def sourceTraceCountingCost (d N : ℕ) (L η : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (3*max 1 (((N:ℝ)+2)^(1-3*η))*(8*L+1)^d))^8

/-- TARGET sumint Step 3: actual fixed/free source core products retain bad and weight gains. -/
theorem exists_source_mixed_core_power_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (hsqrt : Real.sqrt η ≤ gammaBase γ/8)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) → ∀ (t c : ℝ)
      (s : Finset D.S.TVar), s.card ≤ 2 → ∀ x : D.S.TVar → ℝ,
      ENNReal.ofReal (sourceWeightDecay D L γ η)*
        (∏ b : FactorIdx D.S, ∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c (L^(-β)) b z
          ∂Measure.pi (fun j => fixedCoordinateMeasure (s:Set D.S.TVar) x (sourceCoreCoordinateTimeEquiv D ⟨b,j⟩))) ≤
        sourceTraceCountingCost d N L η*ENNReal.ofReal (sourcePositiveMassBudget D G L γ δ) := by
  obtain ⟨G,hG,hfull⟩ := exists_source_all_core_budgets d hd γ hγ η hη hηbase hηsmall hγη
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hfull⟩ := hfull δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p ν r hr hrupper t c s hs x
  have hL1 : 1 ≤ L := by linarith only [hR,hL]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hδone : δ ∈ Ioc (0:ℝ) 1 := ⟨hδ.1,by linarith only [hδ.2]⟩
  have hηγ : η ≤ γ := hηbase.trans (min_le_left _ _)
  have hrone : ‖r‖ ≤ 1 := hrupper.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith only [hηγ]))
  have hh : L^(-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (neg_nonpos.mpr hβ.le)
  have hηp : 0 ≤ 1-3*η := by linarith only [hηsmall]
  have hprod := prod_sourceCore_mixed_le_of_full_budgets D hD (by omega) hG hL1 hγ hδone hηp p ν r hrone
    t c hh s hs x (hfull L hL D A hD p ν r hr hrupper t c)
  calc
    _ ≤ ENNReal.ofReal (sourceWeightDecay D L γ η)*
        (sourceTraceCountingCost d N L η*∏ b : FactorIdx D.S, ENNReal.ofReal (sourceCorePowerBudget D G L γ δ b)) :=
      mul_le_mul' le_rfl hprod
    _ = sourceTraceCountingCost d N L η*(ENNReal.ofReal (sourceWeightDecay D L γ η)*
        ∏ b : FactorIdx D.S, ENNReal.ofReal (sourceCorePowerBudget D G L γ δ b)) := by ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl (weighted_prod_sourceCorePowerBudget_le D hD (by omega) hγ hsqrt
      (zero_le_one.trans hG) hL1 hδ.1)

end WaveTurbulence.Sumint
