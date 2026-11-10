/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1W.Defs

/-! # STAGE1W-GLUE: Inputs (ported by source from the S-STAGE1W probe, see COPIED-SHA256SUMS). -/


@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-! ## 10. The inputs O4′ consumes (verbatim S2-ST / research-internal statements) -/

/-- **Weighted incoherent decay** (verbatim `ResearchInternal.TopIncoherentDecayAt`; INC-TOP's target in the
`GPresented` form). -/
def TopIncoherentDecayAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    ∀ (g : Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → GPresented (32 * P.d) g cψ →
    (∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ (LG : LayeredGarden 2),
      Q.Decodes LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
      1 ≤ LG.incoherency Q.links →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => coupleLeavesTop P.L P.γ P.δ p g q q' LG H (ts 0) (ts 1) k) ≤
        ENNReal.ofReal (cψ ^ (4 * n + 2)) * regBound P n (LG.incoherency Q.links) *
          ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ (LG : LayeredGarden 1),
      X.DecodesTree LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q →
      (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
      1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => treeLeavesTop P.L P.γ P.δ p g q LG H (ts 0) (ts 1) k) ≤
        ENNReal.ofReal (cψ ^ (4 * n + 1)) * regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) *
          ENNReal.ofReal (leafSizeProduct LG B))

/-- **Agreement, trees** (verbatim). -/
def RowTopAgreementTree : Prop :=
  ∀ {d : ℕ} (p q q' : ℕ) (X : RegChain) (LG : LayeredGarden 1), q' ≤ q → q ≤ p → IsCoherentTreeAt p q q' X LG →
    ∀ (g : Mom d → ℂ) (L : ℝ) (k : Mom d) (κ : GenDecoration LG.garden d (fun _ => 0) 0),
      rowTopWeight p g LG ![q] (cosetDecoration LG.garden L k κ.1) = if q' < p ∧ q = p then g k else 1

/-! ## 11. Per-root (per-arm) weights: the input forms O4′ actually needs -/

/-- `rowTopWeight` with one weight per ROOT of the standalone regular object (a couple's two arms may lie in different
original trees, hence carry different frontier scales; Lemma 4.1 allows arbitrary per-vertex scales). -/
def rowTopWeightR {w d : ℕ} (p : ℕ) (g : Fin w → Mom d → ℂ) (LG : LayeredGarden w) (qr : Fin w → ℕ)
    (k : GNode LG.garden.tree → Mom d) : ℂ :=
  ∏ a : GNode LG.garden.tree, topPsi p (g a.1.1) (LG.layer a) (rowParentLayer LG qr a) (k a)

theorem rowTopWeightR_const {w d : ℕ} (p : ℕ) (g : Mom d → ℂ) (LG : LayeredGarden w) (qr : Fin w → ℕ)
    (k : GNode LG.garden.tree → Mom d) : rowTopWeightR p (fun _ => g) LG qr k = rowTopWeight p g LG qr k := rfl

def coupleLeavesTopR (L γ δ : ℝ) {d : ℕ} (p : ℕ) (g : Fin 2 → Mom d → ℂ) (q q' : ℕ) (LG : LayeredGarden 2)
    (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0 (rowTopWeightR p g LG ![q, q'])

/-- **INC-TOP target in the form O4′ needs**: `TopIncoherentDecayAt` with per-arm weights on couples (trees have one
root, so the verbatim tree clause is already per-root). -/
def TopIncoherentDecayAtR (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    ∀ (g : Fin 2 → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ i, GPresented (32 * P.d) (g i) cψ) →
    (∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ (LG : LayeredGarden 2),
      Q.Decodes LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
      1 ≤ LG.incoherency Q.links →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => coupleLeavesTopR P.L P.γ P.δ p g q q' LG H (ts 0) (ts 1) k) ≤
        ENNReal.ofReal (cψ ^ (4 * n + 2)) * regBound P n (LG.incoherency Q.links) *
          ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ (LG : LayeredGarden 1),
      X.DecodesTree LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q →
      (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
      1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => treeLeavesTop P.L P.γ P.δ p (g 0) q LG H (ts 0) (ts 1) k) ≤
        ENNReal.ofReal (cψ ^ (4 * n + 1)) * regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) *
          ENNReal.ofReal (leafSizeProduct LG B))

def TopIncoherentDecayGateR : Prop := WTPrefix TopIncoherentDecayAtR

/-- The verbatim single-weight gate is the constant-weight case of the per-arm one. -/
theorem topIncoherentDecayAt_of_R (P : WTParams) (h : TopIncoherentDecayAtR P) : TopIncoherentDecayAt P := by
  intro p hp n hn g cψ hcψ hg
  exact h p hp n hn (fun _ => g) cψ hcψ (fun _ => hg)

/-- **Agreement, couples, per arm** (COH-TRUNK / O6 target): the single crossing factor sits in the arm whose root
parent layer is `p` (Lemma 5.1, `c(q,q')`), in either order of `q, q'` (root `0` is the `+` root). -/
def RowTopAgreementCoupleR : Prop :=
  ∀ {d : ℕ} (p q q' : ℕ) (Q : RegCpl) (LG : LayeredGarden 2), q ≤ p → q' ≤ p → IsCoherentCoupleAt p q q' Q LG →
    ∀ (g : Fin 2 → Mom d → ℂ) (L : ℝ) (k : Mom d) (κ : GenDecoration LG.garden d (fun _ => 0) 0),
      rowTopWeightR p g LG ![q, q'] (cosetDecoration LG.garden L k κ.1) =
        if q' < p ∧ q = p then g 0 k else if q < p ∧ q' = p then g 1 k else 1


end WaveTurbulence.Flower.Stage1W
