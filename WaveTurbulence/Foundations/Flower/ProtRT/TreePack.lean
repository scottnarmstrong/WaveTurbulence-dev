/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootPack
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildMix
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildMixT
public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ASum
public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ACoh

/-! # RT-GATE (i): the root-cut package of a multi-layer paired tree

D3's `root_pack` (ProtPin/RootPack.lean) for a paired tree whose chain need NOT lie in one layer. The root (layer `ℓ₀`) is
pinned; the closing node `𝔫_b` has layer `ℓb ≤ ℓ₀`; the lone leaf has layer `q' ≤ ℓb`. The pieces are bounded on their
own windows by the mixed-layer gates (`tc_tree_mixed`, `tc_couple_mixed`): the suffix `Ks` on `timeBoxGt ℓb q'`, the
closing-pair products `W e = K_int · Q_r · Q_g` on `timeBoxGt ℓ₀ ℓb`. Their eligibility (layers, windows, coherence
from the canonical ambient) is taken as hypotheses (`rt_root_pack`). The incoherency `g'` is the sum over the pieces;
the closing link is accounted separately (D2c's `incoherency_rootCut`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- A red side couple in its own orientation, on the mixed box of its two parents. -/
theorem rt_coupleR_oriented {θ : ℝ} (f : ℝ → ℝ → ℂ) (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (ℓ₀ ℓb : ℕ) :
    rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (fun x => f (cupR m inner ζ (x 0) (x 1) 0) (cupR m inner ζ (x 0) (x 1) 1)) ≤
      rn θ (timeBox ((tc2aQR m inner ζ ℓ₀ ℓb 0 : ℕ) : ℝ) (tc2aQR m inner ζ ℓ₀ ℓb 1)) (fun x => f (x 0) (x 1)) := by
  refine (rn_mono_set θ (fun x hx => hx.1) _).trans ?_
  by_cases hs : slotSign ζ m.red.1 = 1
  · have h0 : rBase m inner ζ 0 = [m.red.1] := by simp [rBase, hs]
    have h1 : rBase m inner ζ 1 = bPath m inner ++ [m.red.2] := by simp [rBase, hs]
    have hn1 : rBase m inner ζ 1 ≠ [m.red.1] := by rw [h1]; exact tc2a_bPath_ne m inner _ _
    have e : tc2aQR m inner ζ ℓ₀ ℓb 0 = ℓ₀ ∧ tc2aQR m inner ζ ℓ₀ ℓb 1 = ℓb := by
      unfold tc2aQR; rw [if_pos h0, if_neg hn1]; exact ⟨rfl, rfl⟩
    rw [e.1, e.2]
    refine le_of_eq (rn_congr θ fun x _ => ?_)
    simp only [cupR, if_pos h0, if_neg hn1]
  · have h0 : rBase m inner ζ 0 = bPath m inner ++ [m.red.2] := by simp [rBase, hs]
    have h1 : rBase m inner ζ 1 = [m.red.1] := by simp [rBase, hs]
    have hn0 : rBase m inner ζ 0 ≠ [m.red.1] := by rw [h0]; exact tc2a_bPath_ne m inner _ _
    have e : tc2aQR m inner ζ ℓ₀ ℓb 0 = ℓb ∧ tc2aQR m inner ζ ℓ₀ ℓb 1 = ℓ₀ := by
      unfold tc2aQR; rw [if_neg hn0, if_pos h1]; exact ⟨rfl, rfl⟩
    rw [e.1, e.2, ← tc2a_swap_box θ (ℓb : ℝ) ℓ₀ (fun x => f (x 0) (x 1))]
    refine le_of_eq (rn_congr θ fun x _ => ?_)
    simp only [cupR, if_neg hn0, if_pos h1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The same for the green side couple. -/
theorem rt_coupleG_oriented {θ : ℝ} (f : ℝ → ℝ → ℂ) (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (ℓ₀ ℓb : ℕ) :
    rn θ (timeBoxGt (ℓ₀ : ℝ) ℓb) (fun x => f (cupG m inner ζ (x 0) (x 1) 0) (cupG m inner ζ (x 0) (x 1) 1)) ≤
      rn θ (timeBox ((tc2aQG m inner ζ ℓ₀ ℓb 0 : ℕ) : ℝ) (tc2aQG m inner ζ ℓ₀ ℓb 1)) (fun x => f (x 0) (x 1)) := by
  refine (rn_mono_set θ (fun x hx => hx.1) _).trans ?_
  by_cases hs : slotSign ζ m.green.1 = 1
  · have h0 : gBase m inner ζ 0 = [m.green.1] := by simp [gBase, hs]
    have h1 : gBase m inner ζ 1 = bPath m inner ++ [m.green.2] := by simp [gBase, hs]
    have hn1 : gBase m inner ζ 1 ≠ [m.green.1] := by rw [h1]; exact tc2a_bPath_ne m inner _ _
    have e : tc2aQG m inner ζ ℓ₀ ℓb 0 = ℓ₀ ∧ tc2aQG m inner ζ ℓ₀ ℓb 1 = ℓb := by
      unfold tc2aQG; rw [if_pos h0, if_neg hn1]; exact ⟨rfl, rfl⟩
    rw [e.1, e.2]
    refine le_of_eq (rn_congr θ fun x _ => ?_)
    simp only [cupG, if_pos h0, if_neg hn1]
  · have h0 : gBase m inner ζ 0 = bPath m inner ++ [m.green.2] := by simp [gBase, hs]
    have h1 : gBase m inner ζ 1 = [m.green.1] := by simp [gBase, hs]
    have hn0 : gBase m inner ζ 0 ≠ [m.green.1] := by rw [h0]; exact tc2a_bPath_ne m inner _ _
    have e : tc2aQG m inner ζ ℓ₀ ℓb 0 = ℓb ∧ tc2aQG m inner ζ ℓ₀ ℓb 1 = ℓ₀ := by
      unfold tc2aQG; rw [if_neg hn0, if_pos h1]; exact ⟨rfl, rfl⟩
    rw [e.1, e.2, ← tc2a_swap_box θ (ℓb : ℝ) ℓ₀ (fun x => f (x 0) (x 1))]
    refine le_of_eq (rn_congr θ fun x _ => ?_)
    simp only [cupG, if_neg hn0, if_pos h1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

end WaveTurbulence.Flower.ProtRT
