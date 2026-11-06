/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseSeparationBound
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise
/-! Pointwise bounds for the actual coherent leafwise app from the separated source estimate. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set WaveTurbulence.Fourier
open scoped ENNReal

/-- Generic point evaluation for the separated order-zero estimate. -/
theorem enorm_of_leafwiseSeparated (P : WTParams) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ)
    (hη0 : 0 ≤ P.η) (hη : P.η ≤ 1 / 2) (n W : ℕ)
    (T : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℝ) → Mom P.d → ℂ)
    (cost : ℝ) (hcost : 0 < cost) (hsep : LeafwiseSeparated P n W T f cost)
    (ts : Fin 2 → ℝ) (k : Mom P.d) (hts : ts ∈ closure (interior T))
    (hc : Continuous (fun t => f t k)) :
    ‖f ts k‖ₑ ≤ ENNReal.ofReal ((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2 * cost) := by
  exact (enorm_le_mixedRestrictionNorm00_closure_interior hη0 T Set.univ f ts k hts
    (mem_univ _) hc).trans (leafwiseSeparated_norm00_le P hC hδ hη n W T f cost hcost hsep)

/-- The individual-leaf product is retained in the bound, so a marked remainder
factor survives. Continuity belongs to the fixed app formula, not arbitrary separated witnesses. -/
theorem enorm_leafwise_coherentApp_le (P : WTParams)
    (hsource : LeafwiseCoherentApproximationOrder0At P) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ)
    (hη0 : 0 ≤ P.η) (hη : P.η ≤ 1 / 2)
    {p n q q' : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (hqq' : q' ≤ q) (hqp : q ≤ p)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal)
    (hH : LeafwiseControlled LG H B) (hcost : 0 < leafSizeProduct LG B)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1))
    (k : Mom P.d) :
    ‖LeafApp.coherentCouple P.δ LG H Q q q' t s k‖ₑ ≤
      ENNReal.ofReal ((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2 * leafSizeProduct LG B) := by
  let f : (Fin 2 → ℝ) → Mom P.d → ℂ :=
    fun ts k => LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k
  have hsep : LeafwiseSeparated P n (30 * P.d) (timeBox q q') f (leafSizeProduct LG B) :=
    ((hsource p hp n hn).1 Q LG q q' hqq' hqp hsize hcoh H B hH).2.2
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hcont0 := (continuous_LeafApp_coherentCouple P.δ H LG Q q q' k).comp hu
  have hcont : Continuous (fun ts : Fin 2 → ℝ => f ts k) := by
    simpa only [f, Function.comp_def] using hcont0
  have htime : ![t,s] ∈ closure (interior (timeBox (q : ℝ) q')) := by
    rw [closure_interior_timeBox]
    exact ⟨ht, hs⟩
  have hh := enorm_of_leafwiseSeparated P hC hδ hη0 hη n (30 * P.d) (timeBox q q')
    f (leafSizeProduct LG B) hcost hsep ![t,s] k htime hcont
  simpa only [f, Matrix.cons_val_zero, Matrix.cons_val_one] using hh

end WaveTurbulence.LGSpine
