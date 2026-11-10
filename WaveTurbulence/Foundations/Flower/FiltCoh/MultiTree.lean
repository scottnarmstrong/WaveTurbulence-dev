/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.SymbolMass
public import WaveTurbulence.Foundations.Spine.RA1LW.Gate
public import WaveTurbulence.Foundations.Spine.PL2330Draft.TreeInd

/-! # FILT-COH: coherent paired trees across layers (bound only)

The kernel of a coherent regular tree whose chain crosses layers is a product of single-layer tree kernels
(`PL234.tree_block_step`): a top factor in `t`, middle factors at fixed times (spatial profiles) and a bottom
factor in `s`. Main's induction over the blocks (`PL2330.tree_lower_bounds30`) is replayed for the kernel alone,
from the single-layer bounds (`TreeKOracle`) and the trace lemmas of `MultiPieces`, at any weight `θ ∈ [0, 1]`. -/

public section
open WaveTurbulence.Induct
open MeasureTheory Set Finset WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.FiltCoh

open TTree WaveTurbulence.LGSpine WaveTurbulence.PL234 WaveTurbulence.PL2330 WaveTurbulence.Reg WaveTurbulence.Links

variable {d : ℕ}

/-- The single-layer tree bound used by the induction (the tree clause of `single_layer_bounds`). -/
@[expose] def TreeKOracle (d : ℕ) (L γ δ θ : ℝ) (Nmax : ℕ) (C : ℝ) : Prop :=
  ∀ (r q'' n : ℕ), q'' ≤ r → n ≤ Nmax → ∀ X : RegChain, X.wf = true → X.size = 2 * n →
    ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
    (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r) →
    ∀ (H : LeafProfiles 1 d) (B : (Fin 1 × Path) → NNReal), LeafwiseControlled LG H B →
    XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B)

/-- The absorption of one block: `c C^{nB+1} ≤ G^{nB}` when `c C² ≤ G` and `nB ≥ 1`. -/
theorem absorb_kernel_step {c C G δ βT β₂ : ℝ} {nB m₂ : ℕ} (hc1 : 1 ≤ c) (hC : 1 ≤ C) (hG : c * C ^ 2 ≤ G)
    (hδ : 0 ≤ δ) (hβT : 0 ≤ βT) (hβ₂ : 0 ≤ β₂) (hnB : 1 ≤ nB) :
    c * (C * (C * δ) ^ nB * βT) * (G * (G * δ) ^ m₂ * β₂) ≤ G * (G * δ) ^ (nB + m₂) * (βT * β₂) := by
  obtain ⟨k, rfl⟩ : ∃ k, nB = k + 1 := ⟨nB - 1, by omega⟩
  have hC0 : 0 ≤ C := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hCG : C ≤ G := by nlinarith [pow_le_pow_left₀ zero_le_one hC 2]
  have hG0 : 0 ≤ G := le_trans hC0 hCG
  have hkey : c * C ^ (k + 2) ≤ G ^ (k + 1) := by
    have h1 : C ^ k ≤ G ^ k := pow_le_pow_left₀ hC0 hCG k
    calc c * C ^ (k + 2) = C ^ k * (c * C ^ 2) := by ring
      _ ≤ G ^ k * G := mul_le_mul h1 hG (by positivity) (by positivity)
      _ = G ^ (k + 1) := by ring
  have hδp : 0 ≤ δ ^ (k + 1 + m₂) := by positivity
  calc c * (C * (C * δ) ^ (k + 1) * βT) * (G * (G * δ) ^ m₂ * β₂)
      = (c * C ^ (k + 2)) * (G * G ^ m₂ * δ ^ (k + 1 + m₂) * (βT * β₂)) := by ring
    _ ≤ G ^ (k + 1) * (G * G ^ m₂ * δ ^ (k + 1 + m₂) * (βT * β₂)) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = G * (G * δ) ^ (k + 1 + m₂) * (βT * β₂) := by ring

section Induction

variable {L γ δ θ : ℝ} {Nmax : ℕ} {C : ℝ} (O : TreeKOracle d L γ δ θ Nmax C) (hC : 1 ≤ C)
  (hd : 1 ≤ d) (hL : 1 ≤ L) (hθ0 : 0 ≤ θ) (hδ : 0 ≤ δ)
  {LG : LayeredGarden 1} (H : LeafProfiles 1 d) (Bd : (Fin 1 × Path) → NNReal)
  {X₀ : RegChain} {q' q : ℕ} (F : TreeCohFacts LG X₀ q' q) (hqq : q' ≤ q)
  (T' : Set (Fin 2 → ℝ)) (b₀ : ℝ) (hT' : ∀ ts ∈ T', ts + ![b₀, -(q' : ℝ)] ∈ Layered.unitBox)

include O hC hd hL hθ0 hδ F hqq hT'

end Induction

end WaveTurbulence.Flower.FiltCoh
