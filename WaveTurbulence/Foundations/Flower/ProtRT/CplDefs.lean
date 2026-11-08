/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildTraceF
public import WaveTurbulence.Foundations.Flower.MkSlotsO.RootTraceHyp

/-! # RT-GATE: the per-output couple statements (FROZEN for the helpers)

Clause (ii) of `MkSlotsO.RootTraceBoundAt` (ruling R188/R189, F-RT-3): a regular couple whose roots in `Rt ≠ ∅` are
pinned at `s`. On the box `{s ≤ ts j, j ∈ Rt}` a pinned tree does not read its clock, so the clause reduces to two
per-output statements:

* **`RtOne θ c' Ct`** — ONE root pinned (tree `j`, layer `p`, at `s`): the restricted norm in the partner clock `y`
  on the partner window `[q', q'+1]` (partner root in a layer `≤ q'`), in D3's `TcTraceOnF` form with the piece loss
  `L^{4c'}` (`PieceLoss P θ c'`: `θ = η, c' = 0` or `θ = 1/4, c' = 4d`). For `q' = p`, `c' = 0` it is D3's
  `TcTraceOnF` with the windowed ambient (`MkSlotsO.CplAmbient p p p`, i.e. `TcCplAmbS`).
* **`RtBoth θ Ct`** — BOTH roots pinned at `s` (both in layer `p`), `θ = η`: a pointwise bound, with room for two cuts
  and two lost root links.

`rtWin p q' j`: the windows (parent layers) of the two trees — `p` for the pinned tree `j`, `q'` for the partner. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtRT

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtPin
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The windows of a couple with pinned tree `j` (window `p`) and partner window `q'`. -/
def rtWin (p q' : ℕ) (j : Fin 2) (t : Fin 2) : ℕ := if t = j then p else q'

/-- **One root pinned**: the root of tree `j` (layer `p`, branching) pinned at `s ∈ (p, p+1)`, the partner tree at its
clock `y` in the window `[q', q'+1]`, in the windowed signed ambient; per output `k`, with D3's output weight
`tcWt`, the piece loss `L^{4c'}` and one lost root link `L`. -/
def RtOne (θ c' Ct : ℝ) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hFC : TcFC P)
    (_hC11 : 1 ≤ P.C₁) (_hθc : PieceLoss P θ c')
    {p : ℕ} (_hp : p < P.D) {nr : ℕ} (_hn : nr ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LGc : LayeredGarden 2)
    (_hwf : Q.wf = true) (_hsz : Q.size = 2 * nr) (_hdec : Q.Decodes LGc.garden) (_hle : ∀ a, LGc.layer a ≤ p)
    (j : Fin 2) {q' : ℕ} (_hq' : q' ≤ p)
    (_hamb : MkSlotsO.CplAmbient p (rtWin p q' j 0) (rtWin p q' j 1) Q LGc)
    (_hj : layerAt LGc (j, []) = p) (_hjb : ([] : TTree.Path) ∈ (LGc.garden.tree j).branching)
    (_hr : layerAt LGc (t1sw j, []) ≤ q') {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (_hHc : LeafwiseControlled LGc Hc Bc)
    (S : Finset (GNode LGc.garden.tree)) (ω : GNode LGc.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGc.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGc.garden.tree)) (M : GBranch LGc.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGc.garden.tree)) (Mu : GBranch LGc.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (k : Mom P.d),
    rn θ (win (q' : ℝ)) (fun y => kernelProt P.L P.γ P.δ LGc Hc
        (gateM S ω F M Fu Mu) (fun b => if b.1.1 = j then s else y 0) 0 (trFix j s) k (fun _ => 0) 0) ≤
      ENNReal.ofReal (Ct * (P.L ^ (4 * c') * (P.L * (coupling P.d P.L P.γ P.δ ^ 2 *
        (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) * leafSizeProduct LGc Bc * starCost S cω)))) *
          tcWt P.L k

/-- **Both roots pinned** at `s` (both branching, in layer `p`): a pointwise bound per output `k` (one cut, or two
cuts, each with room for the lost root links). -/
def RtBoth (θ Ct : ℝ) : Prop :=
  ∀ {P : WTParams} {C₁a C₂a C₁b C₂b : ℝ} (_K : AlphaConsts P C₁a C₂a C₁b C₂b) (_hFC : TcFC P)
    (_hC11 : 1 ≤ P.C₁) (_hθc : PieceLoss P θ 0)
    {p : ℕ} (_hp : p < P.D) {nr : ℕ} (_hn : nr ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LGc : LayeredGarden 2)
    (_hwf : Q.wf = true) (_hsz : Q.size = 2 * nr) (_hdec : Q.Decodes LGc.garden) (_hle : ∀ a, LGc.layer a ≤ p)
    (_hamb : MkSlotsO.CplAmbient p p p Q LGc)
    (_hj : ∀ j : Fin 2, layerAt LGc (j, []) = p)
    (_hjb : ∀ j : Fin 2, ([] : TTree.Path) ∈ (LGc.garden.tree j).branching)
    {s : ℝ} (_hps : (p : ℝ) < s) (_hsp : s < p + 1)
    (Hc : LeafProfiles 2 P.d) (Bc : (Fin 2 × TTree.Path) → NNReal) (_hHc : LeafwiseControlled LGc Hc Bc)
    (S : Finset (GNode LGc.garden.tree)) (ω : GNode LGc.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LGc.garden.tree → ℝ) (_hpres : ∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch LGc.garden.tree)) (M : GBranch LGc.garden.tree → ℝ) (_hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch LGc.garden.tree)) (Mu : GBranch LGc.garden.tree → ℝ) (_hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (k : Mom P.d),
    ‖kernelProt P.L P.γ P.δ LGc Hc (gateM S ω F M Fu Mu) (fun _ => s) 0 (MkSlotsO.rootPins (fun _ => True) s) k
        (fun _ => 0) 0‖ₑ ≤
      ENNReal.ofReal (Ct * (P.L ^ 2 * (coupling P.d P.L P.γ P.δ ^ 2 *
          (P.C₁ ^ 3 * rb P (nr - 1) (LGc.incoherency Q.links)) +
        coupling P.d P.L P.γ P.δ ^ 2 * (latC P.d * P.L ^ P.d) ^ 2 *
          (coupling P.d P.L P.γ P.δ ^ 2 * (P.C₁ ^ 6 * rb P (nr - 2) (LGc.incoherency Q.links)))) *
        leafSizeProduct LGc Bc * starCost S cω)) * tcWt P.L k

end WaveTurbulence.Flower.ProtRT
