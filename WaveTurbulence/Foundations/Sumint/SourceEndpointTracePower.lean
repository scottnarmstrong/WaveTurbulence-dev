/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.SourceMixedCorePower
public import WaveTurbulence.Foundations.Sumint.SourceCoreTrace

/-!
# Actual endpoint selected-time traces retain the source power gains

This combines the actual endpoint amplitude reduction with the proved
fixed/free core bounds. No trace, oscillatory mass, or envelope bound is
assumed in the resulting source estimate.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

noncomputable section
local instance {d : ℕ} (D : SumintDatum d) {k : ℕ} (sel : Fin k → D.S.TVar) :
    Fintype {i : D.S.TVar // i ∉ Set.range sel} :=
  @Subtype.fintype D.S.TVar (fun i => i ∉ Set.range sel) (fun _ => Classical.propDecidable _) inferInstance

/-- TARGET sumint Step 3: one or two fixed actual input times retain the source bad and weight gains. -/
theorem exists_source_endpoint_trace_power_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
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
      (k : ℕ), k ≤ 2 → ∀ (sel : Fin k → D.S.TVar) (hsel : Function.Injective sel) (x : Fin k → ℝ),
      (∫⁻ y : {i : D.S.TVar // i ∉ Set.range sel} → ℝ,
        ‖sourceExitInput D hI L γ δ η p ν r c (L^(-β)) upper v ((selectedCoordinateSplit sel hsel).symm (x,y))‖ₑ) ≤
        sourceTraceCountingCost d N L η*ENNReal.ofReal (sourcePositiveMassBudget D G L γ δ) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_mixed_core_power_bound d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p ν r hr hrupper hI c upper v k hk sel hsel x
  have hLp : 0 < L := by linarith only [hR,hL]
  let s : Finset D.S.TVar := Finset.univ.image sel
  have hs : s.card ≤ 2 := (Finset.card_image_le.trans (by simp only [Finset.card_univ,Fintype.card_fin]; exact hk))
  have hset : (s:Set D.S.TVar) = Set.range sel := by
    ext i
    simp only [s,Finset.coe_image,Finset.coe_univ,Set.image_univ]
  have hcore := hbound L hL D A hD p ν r hr hrupper 0 c s hs (selectedFixedVector sel hsel x)
  rw [hset] at hcore
  have ht := (lintegral_sourceExitInput_trace_le D hI hD hLp δ p ν r c (L^(-β)) upper v sel hsel x).trans hcore
  exact ht

end
end WaveTurbulence.Sumint
