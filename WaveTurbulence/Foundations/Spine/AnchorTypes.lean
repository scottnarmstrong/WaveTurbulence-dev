/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements
public import WaveTurbulence.Frozen.Defs.SumintDatum
public import WaveTurbulence.Frozen.Defs.SumintDatumAdmissible
public import WaveTurbulence.Frozen.Defs.SumintDatumEllVec
public import WaveTurbulence.Frozen.Defs.SumintDatumExpr
public import WaveTurbulence.Frozen.Defs.SumintDatumKVec
public import WaveTurbulence.Frozen.Defs.SumintDatumM0
public import WaveTurbulence.Frozen.Defs.SumintDatumM1
public import WaveTurbulence.Frozen.Defs.SumintDatumPhase
public import WaveTurbulence.Frozen.Defs.SumintDatumTimeDom
public import WaveTurbulence.Frozen.Defs.SumintShape
public import WaveTurbulence.Frozen.Defs.SumintShapeLexLt
public import WaveTurbulence.Frozen.Defs.SumintShapeM
public import WaveTurbulence.Frozen.Defs.SumintShapeN
public import WaveTurbulence.Frozen.Defs.SumintShapeTVar
public import WaveTurbulence.Frozen.Defs.SumintShapeUSlot
public import WaveTurbulence.Frozen.Defs.SumintShapeVIdx
public import WaveTurbulence.Frozen.Defs.SumintShapeX0Slot
public import WaveTurbulence.Frozen.Defs.SumintShapeXSlot
public import WaveTurbulence.Frozen.Defs.SumintShapeYSlot
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! Exact source-anchor proposition aliases for the LG dependency map. No draft theorem is imported.
These aliases are available for source checking; redundant upstream inputs are not automatically part of the minimal spine. -/
@[expose] public section
open WaveTurbulence.Induct
namespace WaveTurbulence.LGSpine
open MeasureTheory Finset Set
open scoped Classical ENNReal

/-- TARGET L761–779; snapshot-7 B1.2. Literal snapshot proposition. -/
abbrev LayergardenGate : Prop := Induct.LayergardenGate

/-- TARGET L1145–1232; B2.1. Literal snapshot proposition. -/
abbrev RegularAsymptoticsGate : Prop := WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ r : ℕ, r ≤ p → ∀ R : Mom P.d → ℝ, InputRemainder P R r →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      let F : Mom P.d → ℝ := fun k => P.φ (P.δ * r) k + R k
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a = r) →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            Q.app P.δ r F (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (2) regular trees
      (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
        X.DecodesTree LG.garden → ∀ q' : ℕ, q' ≤ r →
        (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r) →
        XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q') Set.univ
          (fun ts k => KTstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            X.app P.δ r F (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (3) the factors
      (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBox r r) Set.univ
            (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets Q.links,
            SNormR (30 * P.d) (30 * P.d) (Q.Mstar F Z (0, []) (1, [])) ≤
              ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      (∀ X : RegChain, X.wf = true → X.dominant = true → X.size = 2 * n → ∀ ζ : ℤˣ,
        ∀ q' : ℕ, q' ≤ r →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q') Set.univ
            (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets (X.treeLinks ζ),
            SNormR (30 * P.d) 0 (X.Nstar F Z ζ (0, [])) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      -- (4) the WKE identity (corrected regref1-5)
      (r = p → (∀ k, R k = 0) → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
        ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n),
            Q.app P.δ p F t t k =
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ))

end WaveTurbulence.LGSpine
