/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.Flower.IncTop.Top.RootJets
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.AllCoupleDecay
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.TreeDecay

/-! # D5b-3 FILT-GATE: statement layer

The D5 kernels (`ProtDefs.FiltIncoherentDecayAt`): main's leafwise kernel `kernelLeavesW` with the multiplier
`starWeight S ω · filtWeight F ann M · filtWeight Fu false Mu`, and the two filtered star decays that the gate
consumes, at both weights of the gate: `(θ, c) = (η, 0)` and `(1/4, 4d)` (o82 Prop 15.1 `g ≥ 1`, Lemma 16.1).

They are INC-TOP's `exists_KQstarStar_decay` / `exists_KTstarStar_decay` (StarCouple, StarTree) with the filters and
the weight pair; `(θ, c)` is chosen after `L`, as in the gate (one threshold for both weights). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links
open WaveTurbulence.LGSpine WaveTurbulence.IncohLeafwise WaveTurbulence.Flower.IncTop

/-- The D5 multiplier: star weight times the two filter layers. -/
def starFiltMult {w d : ℕ} {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → Star d → ℂ)
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (κ : GNode G.tree → Mom d) : ℂ :=
  starWeight S ω κ * ProtDefs.filtWeight F ann M κ * ProtDefs.filtWeight Fu (fun _ => false) Mu κ

/-- The D5 couple kernel (two root clocks `t`, `s`). -/
def coupleLeavesStarFilt (L γ δ : ℝ) {d : ℕ} (LG : LayeredGarden 2) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Star d → ℂ) (F : Finset (GBranch LG.garden.tree))
    (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (H : LeafProfiles 2 d) (t s : ℝ) (k : Mom d) : ℂ :=
  Stage1W.kernelLeavesW L γ δ LG H (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0
    (fun κ => starWeight S ω κ * ProtDefs.filtWeight F ann M κ * ProtDefs.filtWeight Fu (fun _ => false) Mu κ)

/-- The D5 tree kernel (upper clock `t`, lone time `s`). -/
def treeLeavesStarFilt (L γ δ : ℝ) {d : ℕ} (LG : LayeredGarden 1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Star d → ℂ) (F : Finset (GBranch LG.garden.tree))
    (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (H : LeafProfiles 1 d) (t s : ℝ) (k : Mom d) : ℂ :=
  Stage1W.kernelLeavesW L γ δ LG H (fun _ => t) s k (fun _ => 0) 0
    (fun κ => starWeight S ω κ * ProtDefs.filtWeight F ann M κ * ProtDefs.filtWeight Fu (fun _ => false) Mu κ)

/-- The two weights of the gate: `X^η` with no loss and `X^{1/4}` with loss `L^{4d}`. -/
def GateWeight (d : ℕ) (η θ c : ℝ) : Prop := (θ = η ∧ c = 0) ∨ (θ = 1 / 4 ∧ c = 4 * d)

/-- **Filtered star couple decay** (weighted `exists_KQstarStar_decay` with the D5 filters, both weights). -/
def StarFiltCoupleDecay (d : ℕ) (B : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 100 → (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
    ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ p : ℕ, p ≤ D →
      ∀ Q : RegCpl, ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
      (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
      1 ≤ LG.incoherency Q.links → ∀ H : LeafProfiles 2 d,
      (∀ ℓ ∈ inputLeaves LG.garden,
        Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B) →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, L ≤ Mu b) →
      Fourier.mixedRestrictionNorm θ (30 * d) (30 * d) (timeBox q q') univ
        (fun (ts : timeBox q q') (k : (univ : Set (Mom d))) =>
          coupleLeavesStarFilt L γ δ LG S ω F ann M Fu Mu H (ts.1 0) (ts.1 1) k.1) ≤
        ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (cω a)) *
          ENNReal.ofReal ((C * δ) ^ Q.links.length *
            L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links) * L ^ c)

/-- **Filtered star tree decay** (weighted `exists_KTstarStar_decay` with the D5 filters, both weights). -/
def StarFiltTreeDecay (d : ℕ) (B : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 100 → (100 * (d : ℝ)) ^ 2 * η ≤ 1 →
    ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → η < incoherenceExponent d γ →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ,
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ θ c : ℝ, GateWeight d η θ c → ∀ p : ℕ, p ≤ D →
      ∀ X : RegChain, ∀ LG : LayeredGarden 1, X.DecodesTree LG.garden →
      (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) → ∀ H : LeafProfiles 1 d,
      (∀ ℓ ∈ inputLeaves LG.garden,
        Fourier.spatialNorm (40 * d) (40 * d) (fun k => (H ℓ.1 k : ℂ)) ≤ ENNReal.ofReal B) →
      ∀ (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ)
        (cω : GNode LG.garden.tree → ℝ), (∀ a ∈ S, StarPresented (30 * d) (ω a) (cω a)) →
      ∀ (F : Finset (GBranch LG.garden.tree)) (ann : GBranch LG.garden.tree → Bool)
        (M : GBranch LG.garden.tree → ℝ), (∀ b ∈ F, L ≤ M b) →
      ∀ (Fu : Finset (GBranch LG.garden.tree)) (Mu : GBranch LG.garden.tree → ℝ), (∀ b ∈ Fu, L ≤ Mu b) →
      Fourier.mixedRestrictionNorm θ (30 * d) 0 (timeBoxGt q q') univ
        (fun (ts : timeBoxGt q q') (k : (univ : Set (Mom d))) =>
          treeLeavesStarFilt L γ δ LG S ω F ann M Fu Mu H (ts.1 0) (ts.1 1) k.1) ≤
        ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (cω a)) *
          ENNReal.ofReal ((C * δ) ^ (X.treeLinks (LG.garden.sig 0)).length *
            L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency (X.treeLinks (LG.garden.sig 0))) *
              L ^ c)

end WaveTurbulence.Flower.FiltGate
