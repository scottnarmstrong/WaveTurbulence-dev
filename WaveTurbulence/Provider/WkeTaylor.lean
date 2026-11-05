/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.SNormR
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsLambda
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.WkeTaylorTerm
public import WaveTurbulence.Foundations.WaveB.Bridges
public import WaveTurbulence.Foundations.IncohInst.Regref.SpatialBridge
public import WaveTurbulence.Foundations.WKE.TaylorGateNorm
public import WaveTurbulence.Foundations.WKE.TaylorGateSeries

/-!
# Provider for `WaveTurbulence.wkeTaylor`

The proof of the frozen anchor `WaveTurbulence.wkeTaylor` (T (wketaylor); L752–L758; WAVE-B §5) is assembled here under the export
`WaveTurbulence.Provider.wkeTaylor`: the scratch proof `WkeTaylorGate.wkeTaylor` (V2-CHAIN), moved into this
namespace with its imports renamed. The anchor is SEALED (`by exact WaveTurbulence.Provider.wkeTaylor`). This
module must not import the frozen anchor.
-/

public section

namespace WaveTurbulence.Provider
open MeasureTheory Set Finset
open scoped ENNReal

theorem wkeTaylor : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D →
      let U := wkeTaylorTerm (P.φ (P.δ * p)) P.δ p
      (∀ N, ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k, ∀ x ∈ Finset.Nat.antidiagonalTuple 3 N,
        IntervalIntegrable (fun t' => collisionOp (U (x 0) t') (U (x 1) t') (U (x 2) t') k)
          volume p t) ∧
      (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k, Summable (fun N => |U N t k|) ∧
        ∑' N, U N t k = P.φ (P.δ * t) k) ∧
      ∀ N, ∀ t ∈ Icc (p : ℝ) (p + 1),
        SNormR (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (U N t) ≤
          ENNReal.ofReal (P.C₂ * (P.C₁ * P.δ) ^ N) := by
  intro d hd γ _hγ
  refine ⟨1, zero_lt_one, ?_⟩
  intro η _hη φin _hφin τstar _hτ φ hφ
  have hd2 : 2 ≤ d := by omega
  obtain ⟨B, hB, hbound⟩ := WKE.exists_lowNorm_bound hφ
  let C1 := max 1 (2 * WKE.taylorRate d (2 * d + 1) B)
  have hC1 : 1 ≤ C1 := le_max_left _ _
  refine ⟨C1, hC1, 1, zero_lt_one, ?_⟩
  intro ν _hν
  refine ⟨WKE.taylorStep d B, WKE.taylorStep_pos d B, ?_⟩
  intro δ hδ D _hD htime
  let M := 4 * (40 * d) ^ (D + 1)
  obtain ⟨C2, hC2, hnorm⟩ := WKE.taylor_spatial_bound_all_orders hd2 hφ hB hbound hδ.1 M M
  refine ⟨C2, hC2, 2, le_rfl, ?_⟩
  intro L _hL p hp
  change p < D at hp
  dsimp only
  have hpD : (p : ℝ) + 1 ≤ D := by exact_mod_cast (show p + 1 ≤ D by omega)
  have hpδ : ((p : ℝ) + 1) * δ ≤ τstar := by
    rw [htime]
    exact mul_le_mul_of_nonneg_right hpD hδ.1.le
  have hU (n : ℕ) (t : ℝ) :
      wkeTaylorTerm (φ (δ * p)) δ p n t = ⇑(WKE.taylorU hd2 φ δ p n t) :=
    funext fun k => WaveBBridges.wkeTaylorTerm_eq_taylorU hd2 φ δ p n t k
  refine ⟨?_, ?_, ?_⟩
  · intro N t _ht k x _hx
    simp_rw [hU]
    exact WKE.intervalIntegrable_collision_taylorU hd2 φ δ p (x 0) (x 1) (x 2) k t
  · intro t ht k
    simp_rw [hU]
    exact WKE.taylor_step_series hd2 hφ hbound hδ.1 hδ.2 hpδ ht k
  · intro N t ht
    rw [hU, NormBridgeScratch.SNormR_eq_spatialNorm]
    have horder : 4 * (40 * d) ^ (D + 1 - (p + 1)) ≤ M :=
      Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by omega : 0 < 40 * d) (Nat.sub_le _ _))
    have h := hnorm (4 * (40 * d) ^ (D + 1 - (p + 1))) horder
      (4 * (40 * d) ^ (D + 1 - (p + 1))) horder p hpδ N t ht
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC2)
    apply pow_le_pow_left₀
    · exact mul_nonneg (mul_nonneg (by norm_num) (WKE.taylorRate_nonneg _ _ _)) hδ.1.le
    · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.1.le

end WaveTurbulence.Provider
