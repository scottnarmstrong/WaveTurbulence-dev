/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateInt4

/-! # V5 Step 4d-B: the common lower factor and the sign of the lower joint of the states of `Zp(A)`

`sok_sum`: `SOK` of a finite sum of lower factors.  `Ktil`: the common lower factor `K̃_T` at `A`.  `ktilde_eq`: `K̃^G` is `K̃`
or its exchange according to `twAt`.  `sok_ktilde`: `SOKAt` of `K̃^G` at every state `G ∈ Zp(A)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (RS : CLRegionData G S a b)
  (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (layer : GNode (D.forest hG) → ℕ)
  (hLayer : IsLayering (D.garden hG) layer) (base : Mom d) (t0 t1 t2 : ℝ) (e f : Mom d) (n0 n1 : GNode G.tree)

theorem sok_sum {β : Type*} (s : Finset β) (Φ : β → ℝ → Mom d → Mom d → ℂ)
    (h : ∀ i ∈ s, SOK RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i)) :
    SOK RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (fun t E F' => ∑ i ∈ s, Φ i t E F') := by
  classical
  have hint : ∀ xS, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (fun t E F' => ∑ i ∈ s, Φ i t E F') xS =
      fun σ => ∑ i ∈ s, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) xS σ := by
    intro xS
    funext σ
    simp only [sInt, Finset.mul_sum]
  refine ⟨fun xS => ?_, ?_⟩
  · rw [hint xS]
    exact integrable_finset_sum s (fun i hi => (h i hi).1 xS)
  · have hb : ∀ xS, ∫ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (fun t E F' => ∑ i ∈ s, Φ i t E F') xS σ‖ ≤
        ∑ i ∈ s, ∫ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) xS σ‖ := by
      intro xS
      rw [hint xS]
      have h1 : ∀ σ, ‖∑ i ∈ s, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) xS σ‖ ≤
          ∑ i ∈ s, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) xS σ‖ := fun σ => norm_sum_le _ _
      calc ∫ σ, ‖∑ i ∈ s, sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) xS σ‖
          ≤ ∫ σ, ∑ i ∈ s, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) xS σ‖ :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun σ => norm_nonneg _)
              (integrable_finset_sum s (fun i hi => ((h i hi).1 xS).norm)) (Filter.Eventually.of_forall h1)
        _ = ∑ i ∈ s, ∫ σ, ‖sInt RS D hG L γ δ F layer hLayer base t0 t1 t2 e f n0 n1 (Φ i) xS σ‖ :=
            integral_finset_sum s (fun i hi => ((h i hi).1 xS).norm)
    exact Summable.of_nonneg_of_le (fun xS => integral_nonneg (fun _ => norm_nonneg _)) hb
      (summable_sum (fun i hi => (h i hi).2))

end WaveTurbulence.VineEstS5B
