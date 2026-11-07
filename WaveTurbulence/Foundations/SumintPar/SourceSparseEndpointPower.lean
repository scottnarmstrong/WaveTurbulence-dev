/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.SourceEndpointSelectedFourier
public import WaveTurbulence.Foundations.SumintPar.SourceSparseEndpointL2

/-!
# Actual sparse endpoint Fourier L2 power bounds

The exact coordinate identities transfer the proved native selected
Fourier bounds to the literal endpoint transforms used by the scalar
one- and two-exit frequency pairings.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- TARGET sumint Step 3: actual sparse endpoint transforms have their uniform one- and two-frequency L2 bounds. -/
theorem exists_source_sparse_endpoint_L2_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (hsqrt : Real.sqrt η ≤ gammaBase γ/8)
    (τstar : ℝ) (hτstar : 0 < τstar) (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) → ∀ (hI : 0 < D.S.I) (c : ℝ) (upper : Bool),
      (∀ (v : D.S.TVar), v ≠ firstTime D hI →
        eLpNorm (fun q : ℝ × ℝ => sourceExitTransform D hI upper v
          (weightedCutoffInput D L γ δ η p ν r) c (L^(-β)) q.1 q.2) 2 ≤
          ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ)) ∧
      eLpNorm (fun s : ℝ => sourceExitTransform D hI upper (firstTime D hI)
        (weightedCutoffInput D L γ δ η p ν r) c (L^(-β)) 0 s) 2 ≤
        ENNReal.ofReal (3*L^(9*(d:ℝ))*sourcePositiveMassBudget D G L γ δ) := by
  obtain ⟨G,hG,hbound⟩ := exists_source_endpoint_selected_fourier_bound d hd γ hγ η hη hηbase hηsmall hγη hsqrt
    τstar hτstar β hβ hβγ hβη hβnormal hhigh
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  obtain ⟨R,hR,hbound⟩ := hbound δ N hδ hτ
  refine ⟨R,hR,?_⟩
  intro L hL D A hD p ν r hr hrupper hI c upper
  have hLp : 0 < L := by linarith only [hR,hL]
  have hηthird : η ≤ 1/3 := by linarith only [hηsmall]
  constructor
  · intro v hv
    rw [eLpNorm_sourceExitTransform_two D hI hLp γ δ η hηthird p ν r c (L^(-β)) upper v hv]
    exact hbound L hL D A hD p ν r hr hrupper hI c upper v 2 (by decide)
      ![v,firstTime D hI] (sourceExitSelectedTwo_injective D hI v hv)
  · rw [eLpNorm_sourceExitTransform_one D hI hLp γ δ η hηthird p ν r c (L^(-β)) upper]
    exact hbound L hL D A hD p ν r hr hrupper hI c upper (firstTime D hI) 1 (by decide)
      (fun _ : Fin 1 => firstTime D hI) (fun _ _ _ => Subsingleton.elim _ _)

end WaveTurbulence.SumintPar
