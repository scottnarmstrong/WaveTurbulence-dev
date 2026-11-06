/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelContinuity
public import WaveTurbulence.Foundations.Spine.TimeBoxGeometry
public import WaveTurbulence.Foundations.Spine.XNormPointwise
/-! Consume the source mixed-norm estimate on the literal couple kernel, including box endpoints. -/
public section
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set
open scoped ENNReal

theorem norm_KQstar_le_of_XNormRestr {d : ℕ} (L γ δ θ : ℝ) (hθ : 0 ≤ θ)
    (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (hplain : LG.garden.IsPlain)
    (q q' t s C : ℝ) (A B : ℕ) (k : Mom d)
    (ht : t ∈ Icc q (q + 1)) (hs : s ∈ Icc q' (q' + 1)) (hC : 0 ≤ C)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|)
    (hX : XNormRestr θ A B (timeBox q q') Set.univ
      (fun ts k => KQstar L γ δ F LG (ts 0) (ts 1) k) ≤ ENNReal.ofReal C) :
    ‖KQstar L γ δ F LG t s k‖ ≤ C := by
  have htime : ![t, s] ∈ closure (interior (timeBox q q')) := by
    rw [closure_interior_timeBox]
    exact ⟨ht, hs⟩
  have h := (enorm_le_XNormRestr_of_continuous hθ A B (timeBox q q') Set.univ
    (fun ts k => KQstar L γ δ F LG (ts 0) (ts 1) k) ![t, s] k htime (mem_univ _)
    (continuous_KQstar_time L γ δ F LG hplain k hF)).trans hX
  have h' : ENNReal.ofReal ‖KQstar L γ δ F LG t s k‖ ≤ ENNReal.ofReal C := by
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, ofReal_norm] using h
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp h'

end WaveTurbulence.LGSpine
