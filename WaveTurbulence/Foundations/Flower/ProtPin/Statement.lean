/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentApp

/-! # D3 PROT-PIN: statements

* `ProtBoundAlphaAt` — milestone α of D3: `ProtDefs.ProtBoundAt` for the configurations `none`/`term`, with no
  star weights and no filters (`S = F = Fu = ∅`); the dagger `ind` is kept. Its binders and conclusion are those of
  `ProtBoundAt` verbatim (R172: with `ProtAmbient`), with the hypotheses `cfg ∈ {none, term}`, `S = ∅`, `F = ∅`,
  `Fu = ∅` added.
* `CohFlatAt` — FiltCoh's single-layer coherent oracles (`FiltCoh.D5CoupleKOracle`/`D5TreeKOracle`, READY d5d-d2)
  in prefix form: couples with all nodes in one layer `r`, paired trees with all nodes in `r` except the lone leaf in
  `q'' ≤ r`; star weights and two filter layers; every `0 ≤ θ ≤ 1/4`; no loss. Coherent protected objects and the
  coherent pieces of their cuts are flat in this sense (layerreg in the canonical ambient, `Flat.lean`). Proved
  unconditionally in `CohGate.lean`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs

/-! ### The time box of a configuration (R176) -/

theorem box_of_pinsRoot_false {cfg : ProtCfg} {X : RegChain} (h : cfg.pinsRoot X = false) (t p q' : ℝ) :
    cfg.box X t p q' = timeBoxGt p q' := by
  unfold ProtCfg.box
  rw [h]
  rfl

theorem box_of_pinsRoot {cfg : ProtCfg} {X : RegChain} (h : cfg.pinsRoot X = true) (t p q' : ℝ) :
    cfg.box X t p q' = {ts | ts ∈ timeBoxGt p q' ∧ t ≤ ts 0} := by
  unfold ProtCfg.box
  rw [h]
  rfl

theorem box_none (X : RegChain) (t p q' : ℝ) : ProtCfg.none.box X t p q' = timeBoxGt p q' := rfl
theorem box_term (X : RegChain) (t p q' : ℝ) : ProtCfg.term.box X t p q' = timeBoxGt p q' := rfl
theorem box_trace (X : RegChain) (t p q' : ℝ) : ProtCfg.trace.box X t p q' = timeBoxGt p q' := rfl
theorem box_termChild (i : Fin 3) (X : RegChain) (t p q' : ℝ) :
    (ProtCfg.termChild i).box X t p q' = timeBoxGt p q' := rfl
theorem box_root (X : RegChain) (t p q' : ℝ) :
    ProtCfg.root.box X t p q' = {ts | ts ∈ timeBoxGt p q' ∧ t ≤ ts 0} := rfl
theorem box_rootTerm (X : RegChain) (t p q' : ℝ) :
    ProtCfg.rootTerm.box X t p q' = {ts | ts ∈ timeBoxGt p q' ∧ t ≤ ts 0} := rfl

/-- **Milestone α of D3**: `ProtBoundAt` restricted to `cfg ∈ {none, term}` and `S = F = Fu = ∅`. -/
def ProtBoundAlphaAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n →
  ∀ (cfg : ProtCfg), cfg.Valid X LG p → ProtAmbient p X LG → (cfg = .none ∨ cfg = .term) → ∀ (θ c : ℝ),
    (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2 ∧ (cfg = .none ∨ cfg = .term)) →
  ∀ (s t : ℝ), (p : ℝ) < s → s < t → t < p + 1 → ∀ q' : ℕ, q' ≤ p →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) → S = ∅ →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) → F = ∅ →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) → Fu = ∅ →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
    ((cfg = .none ∨ cfg = .root ∨ cfg = .trace) → ∀ κ, ind κ = 1) →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (b₀ c₀ : Mom P.d),
    XNormRestr θ (30 * P.d) 0 (cfg.box X t p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B)

/-- Milestone α as a gate. -/
def ProtBoundAlphaGate : Prop := WTPrefix ProtBoundAlphaAt

/-- **The `none` configuration of `ProtBoundAt`**, with star weights and filters: `ProtDefs.ProtBoundAt P`'s binders
and conclusion verbatim, with the hypothesis `cfg = .none` added. -/
def ProtBoundNoneAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n →
  ∀ (cfg : ProtCfg), cfg.Valid X LG p → ProtAmbient p X LG → cfg = .none → ∀ (θ c : ℝ),
    (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2 ∧ (cfg = .none ∨ cfg = .term)) →
  ∀ (s t : ℝ), (p : ℝ) < s → s < t → t < p + 1 → ∀ q' : ℕ, q' ≤ p →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
    ((cfg = .none ∨ cfg = .root ∨ cfg = .trace) → ∀ κ, ind κ = 1) →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (b₀ c₀ : Mom P.d),
    XNormRestr θ (30 * P.d) 0 (cfg.box X t p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B)

/-- The `none` configuration as a gate. -/
def ProtBoundNoneGate : Prop := WTPrefix ProtBoundNoneAt

/-- **The configurations `none` and `term` of `ProtBoundAt`** (the two configurations with weight `1/4`), with star
weights, filters and the dagger: `ProtDefs.ProtBoundAt P`'s binders and conclusion verbatim, with the hypothesis
`cfg = .none ∨ cfg = .term` added. -/
def ProtBoundNTAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ (w : ℕ) (LG : LayeredGarden w) (X : RegChain),
  ProtShape p X LG → protSize X LG = 2 * n →
  ∀ (cfg : ProtCfg), cfg.Valid X LG p → ProtAmbient p X LG → (cfg = .none ∨ cfg = .term) → ∀ (θ c : ℝ),
    (θ = P.η ∧ c = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ c = 47 * P.d + 2 ∧ (cfg = .none ∨ cfg = .term)) →
  ∀ (s t : ℝ), (p : ℝ) < s → s < t → t < p + 1 → ∀ q' : ℕ, q' ≤ p →
  ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
    (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
  ∀ (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
  ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
  ∀ (ind : (GNode LG.garden.tree → Mom P.d) → ℝ), TermChildIndicator X ind →
    ((cfg = .none ∨ cfg = .root ∨ cfg = .trace) → ∀ κ, ind κ = 1) →
  ∀ (H : LeafProfiles w P.d) (B : (Fin w × TTree.Path) → NNReal), LeafwiseControlled LG H B →
  ∀ (b₀ c₀ : Mom P.d),
    XNormRestr θ (30 * P.d) 0 (cfg.box X t p q') (latticeBall P.L b₀ c₀)
      (fun ts k => kernelProt P.L P.γ P.δ LG H
        (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ c) * regBound P n (protIncoh X LG) *
        ENNReal.ofReal (leafSizeProduct LG B)

/-- The configurations `none` and `term` as a gate. -/
def ProtBoundNTGate : Prop := WTPrefix ProtBoundNTAt

/-- **The flat coherent bound** (FiltCoh's single-layer oracles `D5CoupleKOracle`/`D5TreeKOracle` in prefix form):
regular couples with every node in one layer `r`, and regular paired trees with every node in `r` except the lone
leaf in `q'' ≤ r`; star weights presented with `30d` moments, two filter layers with scales `≥ L`; every
`0 ≤ θ ≤ 1/4`; bound `(∏ cω) · regBound P n 0 · leafSize` (no `L` power). -/
def CohFlatAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / 4 →
    (∀ (r : ℕ) (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ (LG : LayeredGarden 2),
      Q.Decodes LG.garden → (∀ a, LG.layer a = r) →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun b => if b.1.1 = 0 then ts 0 else ts 1)
          0 k (fun _ => 0) 0 (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ *
            filtWeight Fu (fun _ => false) Mu κ)) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (r q'' : ℕ) (X : RegChain), q'' ≤ r → X.wf = true → X.size = 2 * n → ∀ (LG : LayeredGarden 1),
      X.DecodesTree LG.garden → (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q'' else r) →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Flower.IncTop.Star P.d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, Flower.IncTop.StarPresented (30 * P.d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, P.L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, P.L ≤ Mu b) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal), LeafwiseControlled LG H B →
      XNormRestr θ (30 * P.d) 0 (timeBoxGt r q'') Set.univ
        (fun ts k => Flower.Stage1W.kernelLeavesW P.L P.γ P.δ LG H (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
          (fun κ => Flower.IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ)) ≤
        (∏ a ∈ S, ENNReal.ofReal (cω a)) * regBound P n 0 * ENNReal.ofReal (leafSizeProduct LG B))

/-- The flat coherent bound as a gate. -/
def CohFlatGate : Prop := WTPrefix CohFlatAt

end WaveTurbulence.Flower.ProtPin
