/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.MultiGlue
public import WaveTurbulence.Foundations.Flower.FiltCoh.StarOracle

/-! # FILT-COH (c5): the single-layer oracle interface with the D5 multiplier

`D5CoupleKOracle`, `D5TreeKOracle`: the single-layer bounds with the multiplier `d5Mult` (star weights and the two
filter layers of `ProtDefs.FiltCoherentBoundAt`) that the multi-layer replay consumes (the analogues of
milestone (a)'s `CoupleKOracle`/`TreeKOracle`). `d5Mult_empty`: without filters the multiplier is the star weight,
so `single_layer_star_bounds` is the `F = Fu = ∅` case. -/

public section
open WaveTurbulence.Induct
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory Set TTree WaveTurbulence.Fourier
open WaveTurbulence.RA1Leafwise LGSpine
open scoped ENNReal

/-- Single-layer couples with the D5 multiplier. -/
@[expose] def D5CoupleKOracle (d : ℕ) (L γ δ θ : ℝ) (Nmax : ℕ) (C : ℝ) : Prop :=
  ∀ (r n : ℕ), n ≤ Nmax → ∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n →
    ∀ LG : LayeredGarden 2, Q.Decodes LG.garden → (∀ a, LG.layer a = r) →
    ∀ (H : LeafProfiles 2 d) (B : (Fin 2 × Path) → NNReal), LeafwiseControlled LG H B →
    ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
      (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, IncTop.StarPresented (30 * d) (ω a) (cω a)) →
    ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
      (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, L ≤ M b) →
    ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, L ≤ Mu b) →
    XNormRestr θ (30 * d) (30 * d) (timeBox r r) Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k
        (fun _ => 0) 0 (d5Mult S ω F ann M Fu Mu)) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B) * ∏ a ∈ S, ENNReal.ofReal (cω a)

/-- Single-layer paired trees (lone leaf in a layer `q'' ≤ r`) with the D5 multiplier. -/
@[expose] def D5TreeKOracle (d : ℕ) (L γ δ θ : ℝ) (Nmax : ℕ) (C : ℝ) : Prop :=
  ∀ (r q'' n : ℕ), n ≤ Nmax → ∀ X : RegChain, q'' ≤ r → X.wf = true → X.size = 2 * n →
    ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
    (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r) →
    ∀ (H : LeafProfiles 1 d) (B : (Fin 1 × Path) → NNReal), LeafwiseControlled LG H B →
    ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → IncTop.Star d → ℂ)
      (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, IncTop.StarPresented (30 * d) (ω a) (cω a)) →
    ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
      (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, L ≤ M b) →
    ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, L ≤ Mu b) →
    XNormRestr θ (30 * d) 0 (timeBoxGt r q'') Set.univ
      (fun ts k => Flower.Stage1W.kernelLeavesW L γ δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (d5Mult S ω F ann M Fu Mu)) ≤
      ENNReal.ofReal (C * (C * δ) ^ n * leafSizeProduct LG B) * ∏ a ∈ S, ENNReal.ofReal (cω a)

theorem d5Mult_empty {d w : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ)
    (ann : GBranch G.tree → Bool) (M Mu : GBranch G.tree → ℝ) :
    d5Mult S ω ∅ ann M ∅ Mu = IncTop.starWeight S ω := by
  funext κ
  simp [d5Mult, ProtDefs.filtWeight]

end WaveTurbulence.Flower.FiltCoh
