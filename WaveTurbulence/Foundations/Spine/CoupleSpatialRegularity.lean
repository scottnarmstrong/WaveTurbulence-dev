/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelSpatial
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelContinuity
public import WaveTurbulence.Foundations.Spine.LeafwiseLayerInputs
public import WaveTurbulence.Foundations.Spine.SpatialInputBounds
public import WaveTurbulence.Foundations.Spine.TaylorTermContinuity
/-! Spatial regularity of the actual truncated couple sums and Taylor comparison. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset
open scoped ENNReal

theorem contDiff_KQ_spatial {d A B p : ℕ} (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    (γ δ : ℝ) (F : ℕ → Mom d → ℝ) (C : NNReal)
    (hF : ∀ r ≤ p, ContDiff ℝ A (fun k => (F r k : ℂ)))
    (hbound : ∀ r ≤ p, SNormR A B (F r) ≤ ENNReal.ofReal (C : ℝ))
    (hB : d + 1 ≤ B) (LG : LayeredGarden 2) (hcan : IsCanonC (p + 1) LG) (t : ℝ) :
    ContDiff ℝ A (fun k => KQ L γ δ F LG t k) := by
  have hc : ∀ l ∈ inputLeaves LG.garden,
      ContDiff ℝ A (fun k => (layerProfiles LG F l.1 k : ℂ)) := by
    intro l _
    rw [layerProfiles_leaf]
    exact hF _ (hcan.2.1 _)
  have hb : ∀ l ∈ inputLeaves LG.garden,
      SNormR A B (layerProfiles LG F l.1) ≤ ENNReal.ofReal (C : ℝ) := by
    intro l _
    rw [layerProfiles_leaf]
    exact hbound _ (hcan.2.1 _)
  have hs := contDiff_kernelLeaves_spatial hd hL γ δ LG (layerProfiles LG F) (fun _ => C)
    hc hb hB (fun b => if b.1.1 = 0 then t else t) 0 (fun _ => 0) 0
    (card_lone_le_one_of_plain LG.garden hcan.1.1)
  have he : (fun k => kernelLeaves L γ δ LG (layerProfiles LG F)
      (fun b => if b.1.1 = 0 then t else t) 0 k (fun _ => 0) 0) =
      fun k => KQ L γ δ F LG t k := by
    funext k
    simpa only [KQ, KQstar] using kernelLeaves_layerProfiles L γ δ LG F
      (fun b => if b.1.1 = 0 then t else t) 0 k (fun _ => 0) 0
  rw [he] at hs
  exact hs

theorem contDiff_truncSumC_spatial (P : WTParams) {A B p : ℕ} (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (F : ℕ → Mom P.d → ℝ) (C : NNReal)
    (hF : ∀ r ≤ p, ContDiff ℝ A (fun k => (F r k : ℂ)))
    (hbound : ∀ r ≤ p, SNormR A B (F r) ≤ ENNReal.ofReal (C : ℝ))
    (hB : P.d + 1 ≤ B) (N : ℕ) (t : ℝ) :
    ContDiff ℝ A (fun k => truncSumC P F (p + 1) N t k) := by
  classical
  have he : (fun k => truncSumC P F (p + 1) N t k) =
      fun k => ∑ LG ∈ (Canon.finite_truncSumC_support P (p + 1) N).toFinset,
        KQ P.L P.γ P.δ F LG t k :=
    funext (Canon.truncSumC_eq_sum P F (p + 1) N t)
  rw [he]
  apply ContDiff.sum
  intro LG hLG
  have hm := (Canon.finite_truncSumC_support P (p + 1) N).mem_toFinset.mp hLG
  exact contDiff_KQ_spatial hd hL P.γ P.δ F C hF hbound hB LG hm.1 t

theorem contDiff_wkeTaylorTerm_spatial {d A : ℕ} (hd : 2 ≤ d)
    (φ : ℝ → SchwartzMap (Mom d) ℝ) (δ : ℝ) (p n : ℕ) (t : ℝ) :
    ContDiff ℝ A (fun k => (wkeTaylorTerm (φ (δ * p)) δ p n t k : ℂ)) := by
  simp_rw [WaveBBridges.wkeTaylorTerm_eq_taylorU hd φ δ p n]
  exact Complex.ofRealCLM.contDiff.comp ((WKE.taylorU hd φ δ p n t).smooth A)

end WaveTurbulence.LGSpine
