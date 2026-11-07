/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Pointwise
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelContinuity
public import WaveTurbulence.Foundations.RegularAsymptotics.PairedTreeContinuity

/-! # B3: pointwise values of `KQstar` / `KTstar` on the whole time box

LG-SPINE's `continuous_KQstar_time` / `continuous_KTstar_time` (continuity in `(t, s)` of the actual
decoration sums, proved by dominated convergence from the summable input majorant, valid on the whole
plane, in particular on the diagonal `t = s`) combine with the pointwise bound of `Pointwise` to give
the value of the kernel at every point of the closed time box from its restriction norm.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.LGSpine MeasureTheory Set
open scoped ENNReal

/-- Couple kernel: pointwise bound on `closure (interior T)` by the order-zero restriction norm. -/
theorem enorm_KQstar_le {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2)
    (hplain : LG.garden.IsPlain) {θ : ℝ} (hθ : 0 ≤ θ) (T : Set (Fin 2 → ℝ)) (K : Set (Mom d))
    (hF : ∀ k, ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|)
    (ts : Fin 2 → ℝ) (hts : ts ∈ closure (interior T)) (k : Mom d) (hk : k ∈ K) :
    ‖KQstar L γ δ F LG (ts 0) (ts 1) k‖ₑ ≤
      XNorm00Restr θ T K (fun ts k => KQstar L γ δ F LG (ts 0) (ts 1) k) :=
  enorm_le_XNorm00Restr_of_continuous hθ T K _ ts k hts hk
    (continuous_KQstar_time L γ δ F LG hplain k (hF k))

/-- Paired-tree kernel: pointwise bound on `closure (interior T)` by the order-zero restriction norm. -/
theorem enorm_KTstar_le {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1)
    (hT : IsPairedTree LG.garden) {θ : ℝ} (hθ : 0 ≤ θ) (T : Set (Fin 2 → ℝ)) (K : Set (Mom d))
    (hF : ∀ k, ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|)
    (ts : Fin 2 → ℝ) (hts : ts ∈ closure (interior T)) (k : Mom d) (hk : k ∈ K) :
    ‖KTstar L γ δ F LG (ts 0) (ts 1) k‖ₑ ≤
      XNorm00Restr θ T K (fun ts k => KTstar L γ δ F LG (ts 0) (ts 1) k) :=
  enorm_le_XNorm00Restr_of_continuous hθ T K _ ts k hts hk
    (continuous_KTstar_time L γ δ F LG hT k (hF k))

end WaveTurbulence.VineEstS3
