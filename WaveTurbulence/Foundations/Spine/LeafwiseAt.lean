/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
public import WaveTurbulence.Foundations.Spine.XNormWeightPointwise
/-! Literal fixed-P bodies of the exported leafwise source gates. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Set Finset
open scoped ENNReal

abbrev LeafwiseRegularAsymptoticsAt (P : WTParams) : Prop :=
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

theorem LeafwiseRegularAsymptoticsAt_gate_eq : LeafwiseRegularAsymptoticsGate = WTPrefix LeafwiseRegularAsymptoticsAt := rfl

/-- The order-zero consequence of `LeafwiseCoherentApproximationAt` (the pre-R33 form, consumed by the
order-zero spine modules): weighted `XNorm00Restr` of the coherent error. -/
abbrev LeafwiseCoherentApproximationOrder0At (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      ∀ (H : LeafProfiles 2 P.d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      (XNorm00Restr P.η (timeBox q q') Set.univ
        (fun ts k => ((jbr k ^ (30 * P.d) : ℝ) : ℂ) * (coupleLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentCouple P.δ LG H Q q q' (ts 0) (ts 1) k)) ≤
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
      (XNorm00Restr P.η (timeBoxGt q q') Set.univ
        (fun ts k => treeLeaves P.L P.γ P.δ LG H (ts 0) (ts 1) k -
          LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k) ≤
        regBound P n 1 * ENNReal.ofReal (leafSizeProduct LG B)) ∧
      (X.dominant = false → ∀ ts ∈ timeBoxGt q q', ∀ k,
        LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k = 0) ∧
      LeafwiseSeparated P n 0 (timeBoxGt q q')
        (fun ts k => LeafApp.coherentTree P.δ LG H X q q' (ts 0) (ts 1) k)
        (leafSizeProduct LG B))


/-- R33 F-DERIV: TARGET's literal coherent-error norm `X^{eta,30d,30d}` (couples) / `X^{eta,30d,0}` (trees). -/
abbrev LeafwiseCoherentApproximationAt (P : WTParams) : Prop :=
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


theorem LeafwiseCoherentApproximationAt.toOrder0 {P : WTParams} (h : LeafwiseCoherentApproximationAt P) :
    LeafwiseCoherentApproximationOrder0At P := by
  intro p hp n hn
  obtain ⟨hc, ht⟩ := h p hp n hn
  refine ⟨fun Q LG q q' h1 h2 h3 h4 H B hB => ?_, fun X LG q q' h1 h2 h3 h4 H B hB => ?_⟩
  · obtain ⟨he, hn0, hs⟩ := hc Q LG q q' h1 h2 h3 h4 H B hB
    exact ⟨(XNorm00Restr_weight_le_XNormRestr _ (30 * P.d) (30 * P.d) _ _ _).trans he, hn0, hs⟩
  · obtain ⟨he, hn0, hs⟩ := ht X LG q q' h1 h2 h3 h4 H B hB
    exact ⟨(XNorm00Restr_le_XNormRestr _ (30 * P.d) 0 _ _ _).trans he, hn0, hs⟩

theorem LeafwiseCoherentApproximationAt_gate_eq : LeafwiseCoherentApproximationGate = WTPrefix LeafwiseCoherentApproximationAt := rfl

abbrev LeafwiseIncoherentDecayAt (P : WTParams) : Prop :=
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

theorem LeafwiseIncoherentDecayAt_gate_eq : LeafwiseIncoherentDecayGate = WTPrefix LeafwiseIncoherentDecayAt := rfl

end WaveTurbulence.LGSpine
