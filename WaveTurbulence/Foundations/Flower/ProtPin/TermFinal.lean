/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TermAlpha
public import WaveTurbulence.Foundations.RegStruct.TreeDecodingAuxiliary

/-! # D3 PROT-PIN: `term` for protected paired trees and cap couples, in the frozen norm -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- With the terminal node pinned, the port time is irrelevant (the only lone parent is pinned). -/
theorem kernelProt_port_term {d : ℕ} (L γ δ : ℝ) {LG : LayeredGarden 1} {X : RegChain}
    (hX : X.DecodesTree LG.garden) (H : LeafProfiles 1 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s₁ s₂ s t T : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M up s₁ (ProtCfg.term.fix X s t T) k (fun _ => 0) 0 =
      kernelProt L γ δ LG H M up s₂ (ProtCfg.term.fix X s t T) k (fun _ => 0) 0 := by
  have hset : ∀ s' : ℝ, kDomainFix LG up (ProtCfg.term.fix X s t T) ∩
      {τ | ∀ b, LG.garden.IsLoneParent b → ProtCfg.term.fix X s t T b = none → s' < τ b} =
      kDomainFix LG up (ProtCfg.term.fix X s t T) := by
    intro s'
    refine Set.inter_eq_left.mpr fun τ _ b hb hfix => absurd hfix ?_
    obtain ⟨ℓ, hℓ, h1, i, hi⟩ := hb
    have hl : ℓ.1.2 = X.lonePath := (Reg.decodesTree_lone_iff hX ℓ).1 hℓ
    have hbp : b.1.2 = X.lonePath.dropLast := by rw [← hl, hi, List.dropLast_concat]
    unfold ProtCfg.fix ProtCfg.pins
    rw [if_pos (Nat.lt_one_iff.mp b.1.1.isLt), hbp]
    simp
  unfold kernelProt
  rw [hset s₁, hset s₂]

/-- The constant of `term` at weight `θ` (with the LOE constant `CL`). -/
def termK (CL Cr : ℝ) (d : ℕ) : ℝ := CL * Cr * latC d ^ 2 / 4

theorem termK_nonneg {CL Cr : ℝ} (hCL : 0 ≤ CL) (hCr : 0 ≤ Cr) (d : ℕ) : 0 ≤ termK CL Cr d := by
  unfold termK; positivity

end WaveTurbulence.Flower.ProtPin
