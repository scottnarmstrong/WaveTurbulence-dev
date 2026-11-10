/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.LadFilt.Defs
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedKernelST

/-! # C2 FINALMK-CRUDE: statements

Probe `FinalMKProbe.lean` (current on-disk version, R158) lines 573-662, copied by source (sha256 in
`COPIED-SHA256SUMS`); only namespace and open lines differ. `filterB` is C3's `LadFilt.filterB`; the B0 vocabulary
(`SplicedKernelDataMK`, `splicedKernelMK`) is imported from `MkDefs.Stage1MK`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.Flower.MkDefs (SplicedKernelDataMK splicedKernelMK splicedTimeIntegralMK)
open WaveTurbulence.Flower.LadFilt (LadderL1AtFilt filterB)

/-- Admissible atom weights (S-MARKED `AtomOK`, `lb` gone): filters only at non-hinge atoms, scale `≥ 1`, `|ψ| ≤ 1`,
`𝔟 ψ ≤ cθ`; indicators in `[0,1]` depending only on the bonds at the atoms of `prot`. -/
def AtomOK {w d : ℕ} {G : Garden w} (D : SplicedKernelDataMK G d)
    (prot : Finset (GBranch G.tree)) (cθ : ℝ) : Prop :=
  (∀ a q, D.filt a = some q → a ∉ D.hinges ∧ 1 ≤ q.1 ∧ (∀ u, ‖q.2 u‖ ≤ 1) ∧ filterB ⇑q.2 ≤ cθ) ∧
  (∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1) ∧
  ∀ k k', (∀ a ∈ prot, ∀ i : Fin 3, k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) → D.ind k = D.ind k'

/-! ### C2: the crude bound (finalsbest1′, o75 Theorem 7.5′(8)) -/

/-- The geometric premises that main's coarse proof actually uses (`coarse_fixed` reads only these four fields of
`SplicedSourcePremises`; no subpro support, so survivors do not enter the crude bound). -/
structure SplicedGeomPremises {R : ℕ} (G : Garden (2 * R)) : Prop where
  molecule : G.molecule.IsMolecule
  connected : G.molecule.IsConnected
  atom_count : G.molecule.atoms.card = G.order
  bond_count : G.molecule.bonds.card + R = 2 * G.order

/-- **C2 target `CoarseSplicedAtMK`** (o75 (finalsbest1′)): pins `fix` at any times, Schwartz filters (C3's
`filterB ≤ cθ`), dagger indicators local at `split`; maximal ladders split at `hinges ∪ split` (`split ⊇` pins; the
consumer takes `split = B ∪ Π_sb`). Cost `cθ` per atom, `80d` per split atom (o75: `60d+2`). -/
abbrev CoarseSplicedAtMK (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelDataMK G P.d) (split : Finset (GBranch G.tree)) (cθ : ℝ), 1 ≤ cθ →
    SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ v, D.layer v ≤ p) → AtomOK D split cθ →
    (∀ b, (D.fix b).isSome → b ∈ split) →
  ∀ (A : SourceMaximalLadderData G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SplicedGeomPremises G →
    ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (cθ * P.C₁ * Real.sqrt P.δ) ^ G.order *
        P.L ^ (-P.η * A.totalIncoherency D.layer + 80 * P.d * (G.molecule.rho + (D.hinges ∪ split).card))

/-- **The C2 deliverable**, from C3's `ladderL1GateFilt : WTPrefix LadderL1AtFilt`. -/
abbrev CoarseSplicedGateMK : Prop := WTPrefix CoarseSplicedAtMK

end WaveTurbulence.Flower.FinalMKDefs
