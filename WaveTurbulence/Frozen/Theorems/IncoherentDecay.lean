/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib
public import WaveTurbulence.Frozen.Defs.GNode
public import WaveTurbulence.Frozen.Defs.GNodeRoot
public import WaveTurbulence.Frozen.Defs.Garden
public import WaveTurbulence.Frozen.Defs.InputRemainder
public import WaveTurbulence.Frozen.Defs.InputsF
public import WaveTurbulence.Frozen.Defs.KQstar
public import WaveTurbulence.Frozen.Defs.KTstar
public import WaveTurbulence.Frozen.Defs.LayeredGarden
public import WaveTurbulence.Frozen.Defs.LayeredGardenIncoherency
public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.RegBound
public import WaveTurbulence.Frozen.Defs.RegChainDecodesTree
public import WaveTurbulence.Frozen.Defs.RegChainLonePath
public import WaveTurbulence.Frozen.Defs.RegChainTreeLinks
public import WaveTurbulence.Frozen.Defs.RegCplDecodes
public import WaveTurbulence.Frozen.Defs.RegCplLinks
public import WaveTurbulence.Frozen.Defs.RegCplRegChain
public import WaveTurbulence.Frozen.Defs.RegCplSizeRegChainSize
public import WaveTurbulence.Frozen.Defs.RegCplWfRegChainWf
public import WaveTurbulence.Frozen.Defs.TTree
public import WaveTurbulence.Frozen.Defs.TTreeNodes
public import WaveTurbulence.Frozen.Defs.TTreePath
public import WaveTurbulence.Frozen.Defs.TimeBox
public import WaveTurbulence.Frozen.Defs.TimeBoxGt
public import WaveTurbulence.Frozen.Defs.WTParams
public import WaveTurbulence.Frozen.Defs.WTParamsN
public import WaveTurbulence.Frozen.Defs.WTPrefix
public import WaveTurbulence.Frozen.Defs.XNormRestr
public import WaveTurbulence.Provider.IncoherentDecay

/-!
# incoherentDecay

Wave B tier B2 (WaveB2-Statements.lean), source: T Prop `proplayer1`, L953–L956; L946–L951; WAVE-B v2 §4.12; T Def `defkg`. Frozen by ruling D8
(`docs/DECISIONS.md#D8`); do not edit.
-/

public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- **B2.2 `incoherentDecay`** (T Prop `proplayer1`, L953–L956, with the standing assumptions of
L946–L951; WAVE-B v2 §4.12). Under (Π), for `0 ≤ p < 𝔇`, remainders `R_q` (`q ≤ p`) with
`‖R_q‖_{𝔖^{40d,40d}} ≤ L^{-θ_q}`, inputs `F_q = φ(δq) + R_q` and every `n ≤ N_{p+1}^4`:
1. for every well-formed couple code of order `2n` and layered couple decoded by it, with all layers
   `≤ p`, roots in layers `≤ q` and `≤ q'` (`q, q' ≤ p`, T Def `defkg`), and incoherency index `g ≥ 1`:
   `‖K*_𝒬‖_{𝔛^{η,30d,30d}([q,q+1]×[q',q'+1])} ≤ C₁(C₁δ)^n L^{-(γ₁-√η)g}`;
2. for every well-formed tree code of order `2n` and layered paired tree decoded by it, with all layers
   `≤ p`, root layer `≤ q`, lone leaf in layer `q' ≤ q ≤ p` and `g ≥ 1`: the same bound for `K*_𝒯` in
   `𝔛^{η,30d,0}(([q,q+1]×[q',q'+1]) ∩ {t > s})`.
Deviations: (D1) arbitrary layerings (TARGET's standing assumption does not use canonicity for `g ≥ 1`;
to be confirmed by packet L2); (D2) as B2.1 (D4)–(D6). -/
theorem incoherentDecay : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, (∀ q ≤ p, InputRemainder P (R q) q) →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
        1 ≤ LG.incoherency Q.links →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
          regBound P n (LG.incoherency Q.links)) ∧
      -- (2) regular trees
      (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
        X.DecodesTree LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q →
        (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
        1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
        XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
          (fun ts k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
          regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0)))) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact WaveTurbulence.Provider.incoherentDecay
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end WaveTurbulence
-- FROZEN_ANCHOR_SUFFIX_END
