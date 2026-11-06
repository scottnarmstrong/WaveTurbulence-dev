/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.AnchorTypes
public import WaveTurbulence.Foundations.Spine.ExplicitCoherentApps
public import WaveTurbulence.Foundations.Spine.SourceSeparation
public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs
/-! PL23-30D: the two statements of TARGET Prop 6.1 at its literal 30d norm, restated WORD FOR WORD from the
0814 pins `SpineInputs.lean.0814` (`CoherentApproximationGate`) and `LeafwiseSpineInputs.lean.0814`
(`LeafwiseCoherentApproximationGate`), whose sha256 are recorded in `PINS-SHA256`. The bodies are byte-copies;
only the namespace differs (`WaveTurbulence.PL2330Pin`, to avoid the 0936 declarations of the same names in
`WaveTurbulence.LGSpine`). Every definition they mention is the one of the current spine, built on snapshot 9. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.PL2330Pin
open WaveTurbulence.LGSpine

section Common
open MeasureTheory Set Finset
open scoped ENNReal Classical

/-- TARGET Prop 6.1, L1097–1111, with explicit products (prooflayer1-1–2), L1241–1246,
and the B2 single-layer functions (regref1-3), L1156–1160. The eligible objects are precisely
coherent regular objects embedded in a canonical garden, as required at L951 and layerreg1.
All approximation functions below are the fixed definitions SourceApp.couple / SourceApp.tree. -/
abbrev CoherentApproximationGate : Prop := WTPrefix fun P =>
  ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ,
    (∀ r ≤ p, InputRemainder P (R r) r) →
  ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
    (∀ (Q : RegCpl) (LG : LayeredGarden 2) (q q' : ℕ),
      q' ≤ q → q ≤ p → Q.size = 2 * n → IsCoherentCoupleAt p q q' Q LG →
      (XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
        (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      (Q.dominant = false → ∀ ts ∈ timeBox q q', ∀ k,
        SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k = 0) ∧
      SourceSeparated P n (30 * P.d) (timeBox q q')
        (fun ts k => SourceApp.couple P.δ (inputsF P R) LG Q q q' (ts 0) (ts 1) k)) ∧
    (∀ (X : RegChain) (LG : LayeredGarden 1) (q q' : ℕ),
      q' ≤ q → q ≤ p → X.size = 2 * n → IsCoherentTreeAt p q q' X LG →
      (XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
        (fun ts k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k -
          SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      (X.dominant = false → ∀ ts ∈ timeBoxGt q q', ∀ k,
        SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k = 0) ∧
      SourceSeparated P n 0 (timeBoxGt q q')
        (fun ts k => SourceApp.tree P.δ (inputsF P R) LG X q q' (ts 0) (ts 1) k))

end Common

section Leafwise
open Set Finset
open scoped ENNReal

/-- TARGET Prop 6.1 (L1097–1111), prooflayer1-1–2 (L1241–1246), with the individually
modified leaf inputs required at L2065–2067. Slice profile transport retains the original
leaf addresses. Provider: wt-wke, PL234; REGREF is upstream. -/
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

end Leafwise

end WaveTurbulence.PL2330Pin
