/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseCoherentApp
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements
/-! TARGET L2065–2067: author-approved leafwise source estimates. These are separate conditional
inputs, with literal multilinear kernels and explicit B2 approximation formulas. Providers:
REGREF (wt-torus), PL234 (wt-wke). No approximation function is supplied as data. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped ENNReal

/-- Prop 6.1 separation with the product of individual leaf seminorm bounds in the real
momentum factor. The function f is the fixed explicit app at every use below. -/
def LeafwiseSeparated (P : WTParams) (n W : ℕ) (T : Set (Fin 2 → ℝ))
    (f : (Fin 2 → ℝ) → Mom P.d → ℂ) (cost : ℝ) : Prop :=
  ∃ (m : ℕ) (J : Fin m → (Fin 2 → ℝ) → ℂ) (M : Fin m → Mom P.d → ℝ),
    m ≤ 2 ^ n ∧
    (∀ ts ∈ T, ∀ k, f ts k = ∑ i, (P.δ : ℂ) ^ n * J i ts * (M i k : ℂ)) ∧
    (∀ i, XNorm00Restr (V := Unit) (1 - P.η) T Set.univ
      (fun ts _ => J i ts) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
    ∀ i, SNormR (30 * P.d) W (M i) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n * cost)

/-- TARGET regref1–3 (L1145–1232), used leafwise at L2065–2067. The coupled/tree errors
and each explicit momentum factor are multilinear in H, with cost ∏ B_leaf. No common-profile
or free-app surrogate is used. Provider: wt-torus, REGREF. -/
abbrev LeafwiseRegularAsymptoticsGate : Prop := WTPrefix fun P =>
  ∀ p : ℕ, p < P.D → ∀ r : ℕ, r ≤ p → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ (LG : LayeredGarden 2),
      Q.Decodes LG.garden → (∀ a, LG.layer a = r) →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.couple P.δ r H Q (ts 0) (ts 1) k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
      (Q.dominant = true → ∀ Z ∈ specialSets Q.links,
        SNormR (30 * P.d) (30 * P.d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤
          ENNReal.ofReal (P.C₁ * P.C₁ ^ n * leafSizeProduct LG B))) ∧
    (∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ (LG : LayeredGarden 1),
      X.DecodesTree LG.garden → ∀ q' : ℕ, q' ≤ r →
      (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      (XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q') Set.univ
        (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.tree P.δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
      (X.dominant = true → ∀ Z ∈ specialSets (X.treeLinks (LG.garden.sig 0)),
        SNormR (30 * P.d) 0 (LeafApp.chainNstar H Z X (LG.garden.sig 0) (0, [])) ≤
          ENNReal.ofReal (P.C₁ * P.C₁ ^ n * leafSizeProduct LG B)))

/-- TARGET Prop 6.1 (L1097–1111), prooflayer1-1–2 (L1241–1246), with the individually
modified leaf inputs required at L2065–2067. Slice profile transport retains the original
leaf addresses. R33 F-DERIV (supersedes the 2026-11-04 order-zero correction): the literal norm `XNormRestr eta 30d 30d` (couples) / `XNormRestr eta 30d 0` (trees). Provider: wt-wke, PL234; REGREF is upstream. -/
abbrev LeafwiseCoherentApproximationGate : Prop := WTPrefix fun P =>
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
      (Q.dominant = false → ∀ ts ∈ timeBox q q', ∀ k,
        LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k = 0) ∧
      LeafwiseSeparated P n (30 * P.d) (timeBox q q')
        (fun ts k => LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k)
        (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      (XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
      (X.dominant = false → ∀ ts ∈ timeBoxGt q q', ∀ k,
        LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k = 0) ∧
      LeafwiseSeparated P n 0 (timeBoxGt q q')
        (fun ts k => LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k)
        (leafSizeProduct LG B))


/-- TARGET Prop 5.1 (L953–956) in the leafwise form used at L2065–2067. This is the
regular incoherent kernel channel of the same multilinear extension. Provider: wt-torus
(regular-couple leafwise estimates, REGREF, per the owner ruling); PL1 is the common-profile
upstream source packet. The original B2.2 standing root/lone-layer conditions are retained. -/
abbrev LeafwiseIncoherentDecayGate : Prop := WTPrefix fun P =>
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl), Q.wf = true → Q.size = 2 * n → ∀ (LG : LayeredGarden 2),
      Q.Decodes LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
      1 ≤ LG.incoherency Q.links →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k) ≤
        regBound P n (LG.incoherency Q.links) * ENNReal.ofReal (leafSizeProduct LG B)) ∧
    (∀ (X : RegChain), X.wf = true → X.size = 2 * n → ∀ (LG : LayeredGarden 1),
      X.DecodesTree LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
      LG.layer (GNode.root LG.garden.tree 0) ≤ q →
      (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
      1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
      ∀ (H : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k) ≤
        regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))) *
          ENNReal.ofReal (leafSizeProduct LG B))

end WaveTurbulence.LGSpine
