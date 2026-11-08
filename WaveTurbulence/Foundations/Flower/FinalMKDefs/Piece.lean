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
(support with `SubproSupportMK`), the removal order, and the pin/filter/indicator facts (finding F-C0-3). -/
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

/-- The extra exponent of a marked piece (B0 §6, R157): `cP·d·nProt + (60d+2)(2m + 2·nProt) + 2m`. -/
noncomputable def markedExtra {P : WTParams} {R : ℕ} (cP : ℝ) (π : Stage1PieceMK P.d R) : ℝ :=
  cP * P.d * (π.nProt : ℝ) + (60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ)

/-- **C5 target 1, the marked piece bound** (o75 (finalproof1′/2′), θ = 40ν), restating B0's `MarkedPieceBound` with
main's hypotheses (`PieceSmall`, the gates) and every gain kept (needed by the class sum); `cθ^{40ν}` per order. -/
def MarkedPieceBoundAt (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (π : Stage1PieceMK P.d R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SoundMKFull π p base roots cθ → π.Gsb.order ≤ n → ((n : ℝ) + 1) ≤ P.L →
  ∀ (val : ℂ) (s : ℝ), 0 < s → π.RepresentsIntMK n cP tt base roots s val →
    ‖val‖ ≤ s * P.L ^ markedExtra cP π *
      (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)))

/-- The C5 piece deliverable (fixed parameters, main's `stage1_piece_bound_int` pattern). -/
def MarkedPieceTarget : Prop :=
  ∀ (cP cθ : ℝ), 0 ≤ cP → 1 ≤ cθ → ∀ P : WTParams, 1 ≤ P.d → PieceSmall P →
    CoarseSplicedAtMK P → FineSplicedAtMK P → MarkedPieceBoundAt cP cθ P

/-- **C5 target 2, the class sum** (main's `stage1_sum_bound_int` with marked pieces; the per-piece extra is a uniform
`L^X`; the class count is main's `Stage1Counts` on the forgetful data). -/
def MarkedSumBoundAt (cP cθ X : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (S : Stage1DataMK P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl) (s : ℝ), 0 < s →
    (∀ π, SoundMKFull (S.piece π) p base roots cθ) → (∀ π, (S.piece π).Gsb.order ≤ n) → ((n : ℝ) + 1) ≤ P.L →
    (∀ π, (S.piece π).RepresentsIntMK n cP tt base roots s (S.val π)) →
    (∀ π, markedExtra cP (S.piece π) ≤ X) →
    Stage1Counts C₀ P R n S.toData Cl hCl cls →
    P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2 →
    (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2 →
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s * P.L ^ X *
      (4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))))

end WaveTurbulence.Flower.FinalMKDefs
