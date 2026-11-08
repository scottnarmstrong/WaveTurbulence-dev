/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Piece
public import WaveTurbulence.Foundations.Flower.MkDefs.ChiDNorm

/-! # FINALMK-DEFS / PieceSel (packet D7): the selected piece bound and the selected class sum

Copied by source from `scope/C0-FINALMK/probe/FinalMKProbe.lean` (sha256 `9de6afaa…46d0`), lines 909–954
(`RepresentsIntMKSel`, `representsIntMKSel_empty`, `MarkedPieceBoundSelAt`) and 1011–1035 (`MarkedPieceSelTarget`,
`MarkedSumBoundSelAt`). The face vocabulary of lines 956–1009 is already the world's `FinalMKDefs/Fine.lean` (C4a)
and is imported, not copied.

**Deviations (ruling R175, recorded in `COPIED-SHA256SUMS`):** the selected cost `L^{4a}` of both statements is
`L^{(400d)·a}` (o73 (20.3): the moment mass `L^{7(47d+2)a}` of `RepresentsIntMKSel` was missing from the right side),
and `MarkedPieceSelTarget` takes `1 ≤ P.d` (as R161 for `MarkedPieceTarget`).

**Revision R179 (F-B3s-1):** the selected filter is the normalized `chiDN = chiD / chiDNorm` (`MkDefs.ChiDNorm`),
not `chiD`, whose supremum exceeds the bound `1` of `SoundMKFull.filt_ok`.

**Revision R187 (LB-RESTORE-2):** the four selected statements take `lb v = none` at the selected atoms (a selected
atom is integrated by parts; B3s's lower bounds sit on `dParent` trees, which carry no selection).

**Per-tree scales (D7-2, finding F-C5b-1):** `MarkedPieceBoundSelAtT` (new) and `MarkedSumBoundSelAtT`,
`SelSumTargetT` (copied by source from the world's `CompMK/Defs.lean`, see `COPIED-SHA256SUMS`): each selected atom
`v` at its tree's scale `Ms v.1.1`. -/

@[expose] public section
set_option autoImplicit false

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs

-- [copied] D0 RegProbe.lean (sha256 79a89467…) L91-112: `RepresentsIntMKSel`.
/-- **RepresentsIntMKSel** (D0, F-D0-4): the world's `RepresentsIntMK` with the selected residual moments
`∏_{v ∈ sel} (1+|ξ_v|)^{1/18}` inside the weight mass, paid by the `X^{1/4}` slots adjacent to `v` at cost
`L^{7(47d+2)}` per selected vertex (o73 (20.2); U1 `ModesMomentSel`). -/
def RepresentsIntMKSel {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R)
    (sel : Finset (GBranch π.Gsb.tree)) (n : ℕ) (cP : ℝ) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (val : ℂ) : Prop :=
  ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (μ : Measure Ξ) (w : Ξ → ℂ)
    (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Integrable (fun ξ => w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots) μ ∧
    val = ∫ ξ, w ξ * splicedKernelMK π.Gsb (π.dataMK tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∂μ ∧
    Integrable (fun ξ => ‖w ξ‖ * ∏ v ∈ sel, (1 + |freq ξ v|) ^ (1 / 18 : ℝ)) μ ∧
    (∫ ξ, ‖w ξ‖ * ∏ v ∈ sel, (1 + |freq ξ v|) ^ (1 / 18 : ℝ) ∂μ ≤
      (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * P.L ^ (cP * P.d * (π.nProt : ℝ)) *
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s) ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (Stage1Piece.data π.toStage1PieceD tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

/-- With no selected atom, `RepresentsIntMKSel` is the world's `RepresentsIntMK` [proved]. -/
theorem representsIntMKSel_empty {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (n : ℕ) (cP : ℝ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (val : ℂ) :
    RepresentsIntMKSel π ∅ n cP tt base roots s val ↔ π.RepresentsIntMK n cP tt base roots s val := by
  simp [RepresentsIntMKSel, Stage1PieceMK.RepresentsIntMK]

/-- **C5 target 1′ (selected; D7's `MarkedPieceBoundSel` restated like F-C0-4)**: under `PieceSmall` and the gates,
`RepresentsIntMKSel` gives `MarkedPieceBoundAt`'s right side (all gains kept) times `L^{(400d)·a} M₂^{-a/18}`,
`a = #sel` (R175). -/
def MarkedPieceBoundSelAt (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (π : Stage1PieceMK P.d R) (sel : Finset (GBranch π.Gsb.tree)) (M₂ : ℝ), P.L ≤ M₂ →
    (∀ v ∈ sel, π.fix v = none ∧ ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (M₂, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) →
    (∀ v ∈ sel, ∀ v' ∈ sel, v.1.1 = v'.1.1 → v = v') → (∀ v ∈ sel, π.lb v = none) →
  ∀ (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SoundMKFull π p base roots cθ → π.Gsb.order ≤ n → ((n : ℝ) + 1) ≤ P.L →
  ∀ (val : ℂ) (s : ℝ), 0 < s → RepresentsIntMKSel π sel n cP tt base roots s val →
    ‖val‖ ≤ s * P.L ^ markedExtra cP π *
      (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) *
      P.L ^ (400 * (P.d : ℝ) * (sel.card : ℝ)) * M₂ ^ (-((sel.card : ℝ) / 18))

/-- D7's deliverable in C5 form (consumes C2's and C4's exports; FL-FACE, U1, D3/D5 are lemma inputs). -/
def MarkedPieceSelTarget : Prop :=
  ∀ (cP cθ : ℝ), 0 ≤ cP → 1 ≤ cθ → ∀ P : WTParams, 1 ≤ P.d → PieceSmall P →
    CoarseSplicedAtMK P → FineSplicedAtMK P → LadderFourierAtMKFace P → MarkedPieceBoundSelAt cP cθ P

/-- **C5 target 2′, the class sum with selections** (the consumer of `MarkedPieceBoundSelAt`; `a` selected atoms per
piece, all at scale `M₂`). -/
def MarkedSumBoundSelAt (cP cθ X : ℝ) (a : ℕ) (M₂ : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (S : Stage1DataMK P R) (sel : ∀ π, Finset (GBranch (S.piece π).Gsb.tree)) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl) (s : ℝ), 0 < s →
    P.L ≤ M₂ → (∀ π, (sel π).card = a) →
    (∀ π, ∀ v ∈ sel π, (S.piece π).fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, (S.piece π).filt v = some (M₂, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) →
    (∀ π, ∀ v ∈ sel π, ∀ v' ∈ sel π, v.1.1 = v'.1.1 → v = v') → (∀ π, ∀ v ∈ sel π, (S.piece π).lb v = none) →
    (∀ π, SoundMKFull (S.piece π) p base roots cθ) → (∀ π, (S.piece π).Gsb.order ≤ n) → ((n : ℝ) + 1) ≤ P.L →
    (∀ π, RepresentsIntMKSel (S.piece π) (sel π) n cP tt base roots s (S.val π)) →
    (∀ π, markedExtra cP (S.piece π) ≤ X) →
    Stage1Counts C₀ P R n S.toData Cl hCl cls →
    P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2 →
    (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2 →
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s * P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (a : ℝ)) *
      M₂ ^ (-((a : ℝ) / 18)) *
      (4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))))

/-! ## Per-tree selection scales (finding F-C5b-1) -/

/-- **`MarkedPieceBoundSelAtT`** (D7-2, finding F-C5b-1): `MarkedPieceBoundSelAt` with per-tree scales. The selected
atom `v` carries `filt v = (Ms v.1.1, chiDN)` with `L ≤ Ms v.1.1`, and the gain is `∏_{v ∈ sel} Ms(v.1.1)^{-1/18}`.
At `Ms ≡ M₂` it is `MarkedPieceBoundSelAt`. -/
def MarkedPieceBoundSelAtT (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (π : Stage1PieceMK P.d R) (sel : Finset (GBranch π.Gsb.tree)) (Ms : Fin (2 * R) → ℝ),
    (∀ v ∈ sel, P.L ≤ Ms v.1.1) →
    (∀ v ∈ sel, π.fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (Ms v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) →
    (∀ v ∈ sel, ∀ v' ∈ sel, v.1.1 = v'.1.1 → v = v') → (∀ v ∈ sel, π.lb v = none) →
  ∀ (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SoundMKFull π p base roots cθ → π.Gsb.order ≤ n → ((n : ℝ) + 1) ≤ P.L →
  ∀ (val : ℂ) (s : ℝ), 0 < s → RepresentsIntMKSel π sel n cP tt base roots s val →
    ‖val‖ ≤ s * P.L ^ markedExtra cP π *
      (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) *
      P.L ^ (400 * (P.d : ℝ) * (sel.card : ℝ)) * ∏ v ∈ sel, Ms v.1.1 ^ (-(1 / 18 : ℝ))

-- [copied] world CompMK/Defs.lean (sha256 e6896516…) L64-94 (block sha256 35b4d920…): `MarkedSumBoundSelAtT`,
-- `SelSumTargetT`.
/-- **`MarkedSumBoundSelAtT`**: D7's `MarkedSumBoundSelAt` (R175 form, world `FinalMKDefs/PieceSel.lean`) with the
single scale `M₂` replaced by per-tree scales `Ms j` (the selected vertex `v` of tree `v.1.1` carries
`filt v = (Ms v.1.1, chiDN)`, the normalized filter of ruling R179), the selected trees of every piece equal to `T`,
and the gain `∏_{j ∈ T} Ms_j^{-1/18}`.
At `Ms ≡ M₂` it is `MarkedSumBoundSelAt` for pieces whose selected trees are a fixed `T` with `a = #T`. -/
def MarkedSumBoundSelAtT (cP cθ X : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (S : Stage1DataMK P R) (sel : ∀ π, Finset (GBranch (S.piece π).Gsb.tree)) (T : Finset (Fin (2 * R)))
    (Ms : Fin (2 * R) → ℝ) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl) (s : ℝ), 0 < s →
    (∀ j ∈ T, P.L ≤ Ms j) → (∀ π, (sel π).image (fun v => v.1.1) = T) →
    (∀ π, ∀ v ∈ sel π, (S.piece π).fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, (S.piece π).filt v = some (Ms v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) →
    (∀ π, ∀ v ∈ sel π, ∀ v' ∈ sel π, v.1.1 = v'.1.1 → v = v') → (∀ π, ∀ v ∈ sel π, (S.piece π).lb v = none) →
    (∀ π, SoundMKFull (S.piece π) p base roots cθ) → (∀ π, (S.piece π).Gsb.order ≤ n) → ((n : ℝ) + 1) ≤ P.L →
    (∀ π, RepresentsIntMKSel (S.piece π) (sel π) n cP tt base roots s (S.val π)) →
    (∀ π, markedExtra cP (S.piece π) ≤ X) →
    Stage1Counts C₀ P R n S.toData Cl hCl cls →
    P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2 →
    (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2 →
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s * P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ)) *
      (∏ j ∈ T, Ms j ^ (-(1 / 18 : ℝ))) *
      (4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))))

/-- **The D7 input** (`MarkedPieceSelTarget` composed with the class sum, per-tree form): under `1 ≤ d`, `PieceSmall`
and the three marked gates, the selected class sum holds for every uniform extra `X`. -/
def SelSumTargetT : Prop :=
  ∀ (cP cθ : ℝ), 0 ≤ cP → 1 ≤ cθ → ∀ P : WTParams, 1 ≤ P.d → PieceSmall P →
    CoarseSplicedAtMK P → FineSplicedAtMK P → LadderFourierAtMKFace P → ∀ X : ℝ, MarkedSumBoundSelAtT cP cθ X P
-- [end copied]

end WaveTurbulence.Flower.FinalMKDefs
