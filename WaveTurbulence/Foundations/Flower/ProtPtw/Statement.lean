/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs

/-! # D6a PROT-PTW: the statement (o82 Prop 14.2 → Thm 18.2 (18.4))

The pointwise bound of a protected whole object (`ProtShape`) with its optional terminal pin, at most one selected
annular occurrence on its chain (time still integrated), upper filters, star weights and dagger, at every pair of
clocks and every output, with the full incoherency gain: `L^{3r} M₂^{-a}`, `r = [pin] + #Sel`, `a = #Sel`. The kernel
and multiplier are literally those of `ProtDefs.ProtAnnBoundAt` (D6b's export, which interpolates this bound). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Flower.ProtDefs

/-- **D6a export statement** (o82 Prop 14.2, in the form (18.4) consumed by Thm 18.2). -/
def ProtPtwAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n →
  ∀ (pin : Bool) (Sel : Finset (GBranch LG.garden.tree)), (pin = true → X.lonePath ≠ []) →
    (∀ b ∈ Sel, b.1.1.val = 0 ∧ b.1.2 <+: X.lonePath ∧ b.1.2 ≠ X.lonePath ∧
      (pin = true → b.1.2 ≠ X.lonePath.dropLast)) →
    Sel.card ≤ 1 →
  ∀ (M₂ : ℝ), P.L ≤ M₂ → ∀ (s : ℝ),
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
    (pin = false → ∀ κ, ind κ = 1) →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (t₀ t₁ : ℝ) (k : Mom P.d),
    ‖kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ *
          filtWeight (F ∪ Sel) (fun b => decide (b ∈ Sel)) (fun b => if b ∈ Sel then M₂ else M b) κ *
          filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => t₀) t₁ ((if pin then ProtCfg.term else ProtCfg.none).fix X s s t₀) k (fun _ => 0) 0‖ₑ ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) *
        ENNReal.ofReal (P.L ^ (3 * ((if pin then 1 else 0) + Sel.card : ℕ)) * M₂ ^ (-(Sel.card : ℝ))) *
        regBound P n (protIncoh X LG) * ENNReal.ofReal (leafSizeProduct LG B)

/-- The D6a gate. -/
def ProtPtwGate : Prop := WTPrefix ProtPtwAt

end WaveTurbulence.Flower.ProtPtw
