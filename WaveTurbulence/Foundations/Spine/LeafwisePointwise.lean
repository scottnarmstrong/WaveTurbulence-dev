/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseAt
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelContinuity
public import WaveTurbulence.Foundations.Spine.LeafwiseAppContinuity
public import WaveTurbulence.Foundations.RegularAsymptotics.CosetSummability
public import WaveTurbulence.Foundations.Spine.OrderZeroMomentumWeight
public import WaveTurbulence.Foundations.Spine.TimeBoxGeometry
/-! Consume the exported leafwise source estimates at closed-box points, discharging continuity. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set
open scoped ENNReal

theorem LeafwiseControlled.summable_coset {w d : ℕ} {LG : LayeredGarden w}
    {H : LeafProfiles w d} {B : (Fin w × TTree.Path) → NNReal}
    (h : LeafwiseControlled LG H B) {L : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (k : Mom d) :
    ∀ ℓ ∈ inputLeaves LG.garden, Summable fun m : Fin d → ℤ => |H ℓ.1 (k + latticePoint L m)| := by
  intro ℓ hℓ
  exact summable_abs_coset_of_SNormR hL (by omega) (NNReal.coe_nonneg _) (H ℓ.1) (h ℓ hℓ) k

theorem enorm_leafwise_coherent_error_le (P : WTParams)
    (hsource : LeafwiseCoherentApproximationOrder0At P) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
    (hH : LeafwiseControlled LG H B) (t s : ℝ)
    (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) (k : Mom P.d) :
    ‖coupleLeaves P.L P.γ P.δ LG H t s k - LeafApp.coherentCouple P.δ LG H Q q q' t s k‖ₑ ≤
      regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B) := by
  have hX := ((hsource p hp n hn).1 Q LG q q' hqq' hqp hsize hcoh H B hH).1
  have hplain : LG.garden.IsPlain := hcoh.2.1.1.1
  have hK := continuous_coupleLeaves_time P.L P.γ P.δ H LG hplain k (hH.summable_coset hd hL k)
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hA0 := (continuous_LeafApp_coherentCouple P.δ H LG Q q q' k).comp hu
  have hA : Continuous (fun ts : Fin 2 → ℝ =>
      LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k) := by
    simpa only [Function.comp_def] using hA0
  have htime : ![t, s] ∈ closure (interior (timeBox (q : ℝ) q')) := by
    rw [closure_interior_timeBox]
    exact ⟨ht, hs⟩
  have h := (enorm_le_weighted_XNorm00Restr_of_continuous hη (30 * P.d)
    (timeBox q q') Set.univ
    (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
      LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k)
    ![t, s] k htime (mem_univ _) (hK.sub hA)).trans hX
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using h

end WaveTurbulence.LGSpine
