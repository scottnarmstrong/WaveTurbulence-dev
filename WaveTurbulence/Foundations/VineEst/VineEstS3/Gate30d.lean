/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SourceSeparation
public import WaveTurbulence.Foundations.Spine.ExplicitCoherentApps
public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData

/-! # The 30d Prop 6.1 gate (RULINGS R10), named obligation

`CoherentApproximationGate30d` is the 0814 pin `CoherentApproximationGate`
(`/home/scott/wt-scratch/pl234/pinned/SpineInputs.lean.0814`, sha256 54637750345a...) restated word for
word on the snapshot-9 definitions (`XNormRestr` with the F80 guard).  The body (lines 20-41 of the pin)
is copied verbatim.  It is a named obligation; PL23-30D (`/home/scott/wt-scratch/pl23-30d`) proves it.
Sole difference: the name (a distinct name in this packet's namespace).  Environment note: imports `GateDefs`
(verbatim copies of the four B2-statement defs and `SourceSeparated`) instead of `AnchorTypes`/`SourceSeparation`, because
the V4 closure cannot import `WaveB2Draft.Molecules`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.LGSpine MeasureTheory Set Finset
open scoped ENNReal Classical

/-- TARGET Prop 6.1, L1097–1111, with explicit products (prooflayer1-1–2), L1241–1246,
and the B2 single-layer functions (regref1-3), L1156–1160. The eligible objects are precisely
coherent regular objects embedded in a canonical garden, as required at L951 and layerreg1.
All approximation functions below are the fixed definitions SourceApp.couple / SourceApp.tree. -/
abbrev CoherentGateAt (P : WTParams) : Prop :=
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

/-- The named obligation of R10 (proved by PL23-30D `coherentApproximationGate30`): the prefix of `CoherentGateAt`
(the body is the literal 0814 pin body, only the lambda is named). -/
abbrev CoherentApproximationGate30d : Prop := WTPrefix CoherentGateAt

end WaveTurbulence.VineEstS3
