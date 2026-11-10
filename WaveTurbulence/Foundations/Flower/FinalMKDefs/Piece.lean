/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.LadFilt.Defs
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Crude
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Fine

/-! # FINALMK-DEFS / Piece (packet C5a): the marked piece bound and the class sum (C0 design, SCOPE §4.4)

Copied by source from `scope/C0-FINALMK/probe/FinalMKProbe.lean` (sha256 `49bf9d1e…6025`) lines 740-805
(`SoundMKFull`, `markedExtra`, `MarkedPieceBoundAt`, `MarkedPieceTarget`, `MarkedSumBoundAt`); only the header, imports,
namespace/open lines and the closing `end` differ. -/

@[expose] public section
set_option autoImplicit false

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs


/-- **`SoundMKFull`** = B0's `SoundMK` plus what the fine and crude bounds read: main's `Sound` geometry/support fields
(support with `SubproSupportMK`), the removal order, and the pin/filter/indicator facts (finding F-C0-3). Ruling R187
(F-H3-1): the last three fields `lb_free`, `lb_prot`, `lb_layer` for the constant lower bounds `π.lb`. -/
structure SoundMKFull {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (p : ℕ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (cθ : ℝ) : Prop extends SoundMK (P := P) π p where
  molecule : π.Gsb.molecule.IsMolecule
  connected : π.Gsb.molecule.IsConnected
  atom_count : π.Gsb.molecule.atoms.card = π.Gsb.order
  bond_count : π.Gsb.molecule.bonds.card + R = 2 * π.Gsb.order
  structural : π.Cs.Structural
  support : ∀ z : GenDecoration π.Gsb P.d roots 0,
    splicedEpsilon π.Gsb π.Cs.hinges z.1 ≠ 0 →
    splicedGapIndicator π.Gsb (Stage1Piece.data π.toStage1PieceD (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0)
      (fun _ => 0)) P.L P.γ P.η base z.1 ≠ 0 →
    SubproSupportMK π.Gsb π.Cs π.surv P.L P.γ P.η base
      (univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex π.Gsb z.1)
  hingeOutsideFirst : ∀ v ∈ π.Cs.hinges, ∀ i, ¬ (π.Cs.collection i).IsInterior v
  tripleDesignated : π.Cs.TripleDesignated
  hingeNoLoop : π.Cs.HingeNoLoop
  chainOrder : SurvChainOrder π.surv
  fix_prot : ∀ b, (π.fix b).isSome → b ∈ π.surv.prot
  fix_layer : ∀ b t, π.fix b = some t → (π.layer b : ℝ) ≤ t ∧ t ≤ π.layer b + 1
  filt_ok : ∀ a q, π.filt a = some q → a ∉ π.Cs.hinges ∧ 1 ≤ q.1 ∧ (∀ u, ‖q.2 u‖ ≤ 1) ∧ filterB ⇑q.2 ≤ cθ
  ind_ok : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1
  ind_local : ∀ k k', (∀ a ∈ π.surv.joints ∪ π.surv.prot, ∀ i : Fin 3,
    k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) → π.ind k = π.ind k'
  /-- Ruling R187: the lower-bounded atoms are free, protected (so the crude split and the fine `E` already charge
  them) and their bound lies in their layer window. -/
  lb_free : ∀ b, (π.lb b).isSome → π.fix b = none
  lb_prot : ∀ b, (π.lb b).isSome → b ∈ π.surv.prot
  lb_layer : ∀ b x, π.lb b = some x → (π.layer b : ℝ) ≤ x ∧ x ≤ π.layer b + 1

/-- The extra exponent of a marked piece (B0 §6, R157): `cP·d·nProt + (60d+2)(2m + 2·nProt) + 2m`. -/
noncomputable def markedExtra {P : WTParams} {R : ℕ} (cP : ℝ) (π : Stage1PieceMK P.d R) : ℝ :=
  cP * P.d * (π.nProt : ℝ) + (60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ)

end WaveTurbulence.Flower.FinalMKDefs
