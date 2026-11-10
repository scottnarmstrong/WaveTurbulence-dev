/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Coarse.Core
public import WaveTurbulence.Foundations.Spine.FinalCountMonotone
/-! # CoarseSpliced′: TARGET finalsbest1 over `𝒱_γ` (packet L5c)

`coarseSplicedGammaGate : CoarseSplicedGammaGate` (whole range) and `coarseSplicedGateLow : CoarseSplicedGateLow`
(the low half), unconditionally: the family-free core `coarseSplicedCoreGate` implies the statement for any choice
data, in particular for L6's `𝒱_γ` carrier. The same core also implies main's `CoarseSplicedAt` (a consistency check
that the core is not weaker than main's statement). Large-constant monotonicity for `prefix_and`. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence WaveTurbulence.LGSpine

/-- The core statement implies the `𝒱_γ` statement (the premise `subpro` is not used). -/
theorem coarseSplicedGammaAt_of_core {P : WTParams} (h : CoarseSplicedCoreAt P) : CoarseSplicedGammaAt P :=
  fun p hp R hR hRmax G hpl hir hbal hn hnmax D hD hl A base roots hprem =>
    h p hp R hR hRmax G hpl hir hbal hn hnmax D hD hl A base roots hprem.molecule hprem.connected
      hprem.atom_count hprem.bond_count

/-- **CoarseSpliced′ for `0 < γ ≤ 1/2`** (the low-half form consumed by L7). -/
theorem coarseSplicedGateLow : CoarseSplicedGateLow :=
  prefix_map (fun _ h _ => coarseSplicedGammaAt_of_core h) coarseSplicedCoreGate

private theorem premisesGamma_of_largeConstants {P : WTParams} {c₁ c₂ : ℝ} {R : ℕ} {G : Garden (2 * R)}
    {D : SplicedKernelData G P.d} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    (h : SplicedSourcePremisesGamma ({P with C₁ := c₁, C₂ := c₂} : WTParams) G D base roots) :
    SplicedSourcePremisesGamma P G D base roots :=
  ⟨h.molecule, h.connected, h.atom_count, h.bond_count, h.subpro⟩

/-- Large-constant monotonicity of `CoarseSplicedGammaAt` (as main's `coarseSplicedAt_largeConstantMonotone`). -/
theorem coarseSplicedGammaAt_largeConstantMonotone : LargeConstantMonotone CoarseSplicedGammaAt := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirr hbal hn hnmax D hD hlayer A base
    roots hsrc
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirr hbal hn hnmax D hD hlayer A base roots
    (premisesGamma_of_largeConstants hsrc)
  refine h0.trans ?_
  have hc1 : 0 ≤ P.C₁ := by linarith
  have hδ0 : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hL0 : 0 ≤ P.L := by linarith
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL0 _)
  exact mul_le_mul h₂ (pow_le_pow_left₀ (mul_nonneg hc1 hδ0) (mul_le_mul_of_nonneg_right h₁ hδ0) _)
    (pow_nonneg (mul_nonneg hc1 hδ0) _) (by linarith)

/-- Large-constant monotonicity of the low-half body (as L6's `finalCountLow_largeConstantMonotone`). -/
theorem coarseSplicedLow_largeConstantMonotone :
    LargeConstantMonotone (fun P => P.γ ≤ 1 / 2 → CoarseSplicedGammaAt P) :=
  fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ =>
    coarseSplicedGammaAt_largeConstantMonotone P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)

end WaveTurbulence.GammaLow.Famc
