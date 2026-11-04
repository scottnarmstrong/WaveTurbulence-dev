/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB2

/-! # The exact pinned B2.2 proposition, without importing any unfinished theorem -/

@[expose] public section
open MeasureTheory Finset Set
open scoped ENNReal
namespace WaveTurbulence.IncohInst

/-- Exact text of the pinned `incoherentDecay` type. -/
def anchorType : Prop :=
    WTPrefix fun P =>
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
          regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0))))

end WaveTurbulence.IncohInst
