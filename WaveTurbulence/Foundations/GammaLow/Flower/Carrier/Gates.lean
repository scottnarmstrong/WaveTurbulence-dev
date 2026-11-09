/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.Flower.CompMK.Defs
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MKFull

/-! # FLOWER-LOW (packet L8), item E (2/2): the marked gates over `𝒱_γ`

Main's statements of the marked pipeline, copied by source (sha256 in `COPIED-SHA256SUMS`) onto the carrier of
`Carrier/Defs.lean` (pieces `Stage1PieceMKG P R` over `Fama.Stage1PieceGD P.γ`, survivors `SurvivorDataG P.γ`,
class count `Fama.Stage1CountsG`); every name gets the suffix `G`:
* `FinalMKDefs.Fine`: `SubproConclusionsMKG`, `FineSplicedAtMKG`, and the gate **`FineSplicedGateLowMK`** (main's
  `FineSplicedGateHalfMK` with `P.γ ≤ 1 / 2`; PLAN-L8 item H's output);
* `FinalMKDefs.Piece`: `SoundMKFullG`, `markedExtraG`, `MarkedPieceBoundAtG`, `MarkedPieceTargetG`,
  `MarkedSumBoundAtG`;
* `FinalMKDefs.PieceSel`: `RepresentsIntMKSelG`, …, `MarkedSumBoundSelAtTG`, **`SelSumTargetTG`** (item G's target);
* `MkDefs.Stage1MKFull`: **`Stage1ReductionAtMKFullG`** (item I's target; `selMassMK` is main's);
* `CompMK.Defs`: `Stage1ReductionAtMKSelG` (`selMass` is main's).
The family-free gates `CoarseSplicedAtMK` (C2), `LadderFourierAtMKFace` (C4a) and `PieceSmall` are main's. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.CompMK

namespace WaveTurbulence.GammaLow.Flower
open WaveTurbulence.GammaLow.FinalCount

variable {d : ℕ}

/-- Main's `SubproConclusions` with survivors (the per-piece input of the fine bound). -/
structure SubproConclusionsMKG {R : ℕ} {γ : ℝ} (G : Garden (2 * R)) (D : SplicedKernelData G d) (Cs : Src.SubproChoices γ G)
    (S : SurvivorDataG γ G) (L γ' η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) : Prop where
  structural : Cs.Structural
  survivors : S.Structural Cs
  chainOrder : SurvChainOrderG S
  hinges : D.hinges = Cs.hinges
  support : ∀ z : GenDecoration G d roots 0,
    splicedEpsilon G D.hinges z.1 ≠ 0 → splicedGapIndicator G D L γ' η base z.1 ≠ 0 →
    SubproSupportMKG G Cs S L γ' η base (univ.image (fun i => base + latticePoint L (roots i))) (bondIndex G z.1)
  hingeOutsideFirst : ∀ v ∈ Cs.hinges, ∀ i, ¬ (Cs.collection i).IsInterior v
  tripleDesignated : Cs.TripleDesignated
  hingeNoLoop : Cs.HingeNoLoop

/-- **C4 target 2 `FineSplicedAtMKG`** (o75 (finalsbest2′) + o73 Thm 7.3′(3)): main's fine bound for the marked kernel,
extra `L^{2 N_E}` (C1) and `((N+1)L)^{(5d+4)|E|}` (Prop 18.1 and row 12 via FL-FIBER). Filters and indicators are
weights of modulus `≤ 1` in the absolute count (S Lemma 9.4). Ruling R187 (LB-RESTORE-2): the lower-bounded atoms
are exceptional, `(∀ b, (D.lb b).isSome → b ∈ E)` (the consumer's `E = Π_sb` contains them by `SoundMKFullG.lb_prot`). -/
abbrev FineSplicedAtMKG (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelDataMK G P.d) (Cs : Src.SubproChoices P.γ G) (S : SurvivorDataG P.γ G) (E : Finset (GBranch G.tree)),
    SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ v, D.layer v ≤ p) →
    (∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) → (∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1) →
    (∀ b, (D.fix b).isSome → b ∈ E) → (∀ b t, D.fix b = some t → (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1) →
    (∀ b, (D.lb b).isSome → b ∈ E) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SplicedGeomPremises G → SubproConclusionsMKG G D.toSplicedKernelData Cs S P.L P.γ P.η base roots →
    ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order * P.L ^ (2 * (S.m : ℝ)) *
        (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))

/-- **The C4 deliverable** (from `FinalCountGateHalfMK`, `WTPrefix LadderFourierAtMK`, FL-FIBER and the copy-threaded
cover chain). -/
abbrev FineSplicedGateLowMK : Prop := WTPrefix fun P => P.γ ≤ 1 / 2 → FineSplicedAtMKG P

/-- **`SoundMKFullG`** = B0's `SoundMK` plus what the fine and crude bounds read: main's `Sound` geometry/support fields
(support with `SubproSupportMK`), the removal order, and the pin/filter/indicator facts (finding F-C0-3). Ruling R187
(F-H3-1): the last three fields `lb_free`, `lb_prot`, `lb_layer` for the constant lower bounds `π.lb`. -/
structure SoundMKFullG {P : WTParams} {R : ℕ} (π : Stage1PieceMKG P R) (p : ℕ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (cθ : ℝ) : Prop extends SoundMKG π p where
  molecule : π.Gsb.molecule.IsMolecule
  connected : π.Gsb.molecule.IsConnected
  atom_count : π.Gsb.molecule.atoms.card = π.Gsb.order
  bond_count : π.Gsb.molecule.bonds.card + R = 2 * π.Gsb.order
  structural : π.Cs.Structural
  support : ∀ z : GenDecoration π.Gsb P.d roots 0,
    splicedEpsilon π.Gsb π.Cs.hinges z.1 ≠ 0 →
    splicedGapIndicator π.Gsb (Fama.Stage1PieceG.data π.toStage1PieceGD (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0)
      (fun _ => 0)) P.L P.γ P.η base z.1 ≠ 0 →
    SubproSupportMKG π.Gsb π.Cs π.surv P.L P.γ P.η base
      (univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex π.Gsb z.1)
  hingeOutsideFirst : ∀ v ∈ π.Cs.hinges, ∀ i, ¬ (π.Cs.collection i).IsInterior v
  tripleDesignated : π.Cs.TripleDesignated
  hingeNoLoop : π.Cs.HingeNoLoop
  chainOrder : SurvChainOrderG π.surv
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
noncomputable def markedExtraG {P : WTParams} {R : ℕ} (cP : ℝ) (π : Stage1PieceMKG P R) : ℝ :=
  cP * P.d * (π.nProt : ℝ) + (60 * P.d + 2) * (2 * (π.surv.m : ℝ) + 2 * (π.nProt : ℝ)) + 2 * (π.surv.m : ℝ)

/-- **C5 target 1, the marked piece bound** (o75 (finalproof1′/2′), θ = 40ν), restating B0's `MarkedPieceBound` with
main's hypotheses (`PieceSmall`, the gates) and every gain kept (needed by the class sum); `cθ^{40ν}` per order. -/
def MarkedPieceBoundAtG (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (π : Stage1PieceMKG P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SoundMKFullG π p base roots cθ → π.Gsb.order ≤ n → ((n : ℝ) + 1) ≤ P.L →
  ∀ (val : ℂ) (s : ℝ), 0 < s → π.RepresentsIntMK n cP tt base roots s val →
    ‖val‖ ≤ s * P.L ^ markedExtraG cP π *
      (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)))

/-- The C5 piece deliverable (fixed parameters, main's `stage1_piece_bound_int` pattern). -/
def MarkedPieceTargetG : Prop :=
  ∀ (cP cθ : ℝ), 0 ≤ cP → 1 ≤ cθ → ∀ P : WTParams, 1 ≤ P.d → PieceSmall P →
    CoarseSplicedAtMK P → FineSplicedAtMKG P → MarkedPieceBoundAtG cP cθ P

/-- **C5 target 2, the class sum** (main's `stage1_sum_bound_int` with marked pieces; the per-piece extra is a uniform
`L^X`; the class count is main's `Stage1Counts` on the forgetful data). -/
def MarkedSumBoundAtG (cP cθ X : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (S : Stage1DataMKG P R) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl) (s : ℝ), 0 < s →
    (∀ π, SoundMKFullG (S.piece π) p base roots cθ) → (∀ π, (S.piece π).Gsb.order ≤ n) → ((n : ℝ) + 1) ≤ P.L →
    (∀ π, (S.piece π).RepresentsIntMK n cP tt base roots s (S.val π)) →
    (∀ π, markedExtraG cP (S.piece π) ≤ X) →
    Fama.Stage1CountsG C₀ P R n S.toData Cl hCl cls →
    P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2 →
    (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2 →
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s * P.L ^ X *
      (4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))))

/-- **RepresentsIntMKSelG** (D0, F-D0-4): the world's `RepresentsIntMK` with the selected residual moments
`∏_{v ∈ sel} (1+|ξ_v|)^{1/18}` inside the weight mass, paid by the `X^{1/4}` slots adjacent to `v` at cost
`L^{7(47d+2)}` per selected vertex (o73 (20.2); U1 `ModesMomentSel`). -/
def RepresentsIntMKSelG {P : WTParams} {R : ℕ} (π : Stage1PieceMKG P R)
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
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (Fama.Stage1PieceG.data π.toStage1PieceGD tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

/-- With no selected atom, `RepresentsIntMKSelG` is the world's `RepresentsIntMK` [proved]. -/
theorem representsIntMKSel_emptyG {P : WTParams} {R : ℕ} (π : Stage1PieceMKG P R) (n : ℕ) (cP : ℝ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (val : ℂ) :
    RepresentsIntMKSelG π ∅ n cP tt base roots s val ↔ π.RepresentsIntMK n cP tt base roots s val := by
  simp [RepresentsIntMKSelG, Stage1PieceMKG.RepresentsIntMK]

/-- **C5 target 1′ (selected; D7's `MarkedPieceBoundSel` restated like F-C0-4)**: under `PieceSmall` and the gates,
`RepresentsIntMKSelG` gives `MarkedPieceBoundAtG`'s right side (all gains kept) times `L^{(400d)·a} M₂^{-a/18}`,
`a = #sel` (R175). -/
def MarkedPieceBoundSelAtG (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (π : Stage1PieceMKG P R) (sel : Finset (GBranch π.Gsb.tree)) (M₂ : ℝ), P.L ≤ M₂ →
    (∀ v ∈ sel, π.fix v = none ∧ ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (M₂, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) →
    (∀ v ∈ sel, ∀ v' ∈ sel, v.1.1 = v'.1.1 → v = v') → (∀ v ∈ sel, π.lb v = none) →
  ∀ (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SoundMKFullG π p base roots cθ → π.Gsb.order ≤ n → ((n : ℝ) + 1) ≤ P.L →
  ∀ (val : ℂ) (s : ℝ), 0 < s → RepresentsIntMKSelG π sel n cP tt base roots s val →
    ‖val‖ ≤ s * P.L ^ markedExtraG cP π *
      (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) *
      P.L ^ (400 * (P.d : ℝ) * (sel.card : ℝ)) * M₂ ^ (-((sel.card : ℝ) / 18))

/-- D7's deliverable in C5 form (consumes C2's and C4's exports; FL-FACE, U1, D3/D5 are lemma inputs). -/
def MarkedPieceSelTargetG : Prop :=
  ∀ (cP cθ : ℝ), 0 ≤ cP → 1 ≤ cθ → ∀ P : WTParams, 1 ≤ P.d → PieceSmall P →
    CoarseSplicedAtMK P → FineSplicedAtMKG P → LadderFourierAtMKFace P → MarkedPieceBoundSelAtG cP cθ P

/-- **C5 target 2′, the class sum with selections** (the consumer of `MarkedPieceBoundSelAtG`; `a` selected atoms per
piece, all at scale `M₂`). -/
def MarkedSumBoundSelAtG (cP cθ X : ℝ) (a : ℕ) (M₂ : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (S : Stage1DataMKG P R) (sel : ∀ π, Finset (GBranch (S.piece π).Gsb.tree)) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl) (s : ℝ), 0 < s →
    P.L ≤ M₂ → (∀ π, (sel π).card = a) →
    (∀ π, ∀ v ∈ sel π, (S.piece π).fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, (S.piece π).filt v = some (M₂, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) →
    (∀ π, ∀ v ∈ sel π, ∀ v' ∈ sel π, v.1.1 = v'.1.1 → v = v') → (∀ π, ∀ v ∈ sel π, (S.piece π).lb v = none) →
    (∀ π, SoundMKFullG (S.piece π) p base roots cθ) → (∀ π, (S.piece π).Gsb.order ≤ n) → ((n : ℝ) + 1) ≤ P.L →
    (∀ π, RepresentsIntMKSelG (S.piece π) (sel π) n cP tt base roots s (S.val π)) →
    (∀ π, markedExtraG cP (S.piece π) ≤ X) →
    Fama.Stage1CountsG C₀ P R n S.toData Cl hCl cls →
    P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2 →
    (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2 →
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s * P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (a : ℝ)) *
      M₂ ^ (-((a : ℝ) / 18)) *
      (4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))))

/-- **`MarkedPieceBoundSelAtTG`** (D7-2, finding F-C5b-1): `MarkedPieceBoundSelAtG` with per-tree scales. The selected
atom `v` carries `filt v = (Ms v.1.1, chiDN)` with `L ≤ Ms v.1.1`, and the gain is `∏_{v ∈ sel} Ms(v.1.1)^{-1/18}`.
At `Ms ≡ M₂` it is `MarkedPieceBoundSelAtG`. -/
def MarkedPieceBoundSelAtTG (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (π : Stage1PieceMKG P R) (sel : Finset (GBranch π.Gsb.tree)) (Ms : Fin (2 * R) → ℝ),
    (∀ v ∈ sel, P.L ≤ Ms v.1.1) →
    (∀ v ∈ sel, π.fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, π.filt v = some (Ms v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) →
    (∀ v ∈ sel, ∀ v' ∈ sel, v.1.1 = v'.1.1 → v = v') → (∀ v ∈ sel, π.lb v = none) →
  ∀ (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SoundMKFullG π p base roots cθ → π.Gsb.order ≤ n → ((n : ℝ) + 1) ≤ P.L →
  ∀ (val : ℂ) (s : ℝ), 0 < s → RepresentsIntMKSelG π sel n cP tt base roots s val →
    ‖val‖ ≤ s * P.L ^ markedExtraG cP π *
      (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ * P.δ ^ (10 * P.ν)) ^ n * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-(P.ν * P.η) * ((π.gsk : ℝ) + (π.gsb : ℝ))) *
        P.L ^ (-P.η ^ 6 * ((π.Gsb.molecule.rho : ℝ) + (π.Cs.hinges.card : ℝ)) / 4) *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60))) *
      P.L ^ (400 * (P.d : ℝ) * (sel.card : ℝ)) * ∏ v ∈ sel, Ms v.1.1 ^ (-(1 / 18 : ℝ))

/-- **`MarkedSumBoundSelAtTG`**: D7's `MarkedSumBoundSelAtG` (R175 form, world `FinalMKDefs/PieceSel.lean`) with the
single scale `M₂` replaced by per-tree scales `Ms j` (the selected vertex `v` of tree `v.1.1` carries
`filt v = (Ms v.1.1, chiDN)`, the normalized filter of ruling R179), the selected trees of every piece equal to `T`,
and the gain `∏_{j ∈ T} Ms_j^{-1/18}`.
At `Ms ≡ M₂` it is `MarkedSumBoundSelAtG` for pieces whose selected trees are a fixed `T` with `a = #T`. -/
def MarkedSumBoundSelAtTG (cP cθ X : ℝ) (P : WTParams) : Prop :=
  ∀ {p R n : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ (S : Stage1DataMKG P R) (sel : ∀ π, Finset (GBranch (S.piece π).Gsb.tree)) (T : Finset (Fin (2 * R)))
    (Ms : Fin (2 * R) → ℝ) (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (C₀ : ℕ)
    (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl) (s : ℝ), 0 < s →
    (∀ j ∈ T, P.L ≤ Ms j) → (∀ π, (sel π).image (fun v => v.1.1) = T) →
    (∀ π, ∀ v ∈ sel π, (S.piece π).fix v = none ∧
      ∃ ψ : SchwartzMap ℝ ℂ, (S.piece π).filt v = some (Ms v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) →
    (∀ π, ∀ v ∈ sel π, ∀ v' ∈ sel π, v.1.1 = v'.1.1 → v = v') → (∀ π, ∀ v ∈ sel π, (S.piece π).lb v = none) →
    (∀ π, SoundMKFullG (S.piece π) p base roots cθ) → (∀ π, (S.piece π).Gsb.order ≤ n) → ((n : ℝ) + 1) ≤ P.L →
    (∀ π, RepresentsIntMKSelG (S.piece π) (sel π) n cP tt base roots s (S.val π)) →
    (∀ π, markedExtraG cP (S.piece π) ≤ X) →
    Fama.Stage1CountsG C₀ P R n S.toData Cl hCl cls →
    P.C₂ * P.L ^ (-(P.ν * P.η)) ≤ 1 / 2 →
    (((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4) ≤ 1 / 2 →
    ‖@Finset.sum S.Pc ℂ _ (@univ S.Pc S.fin) S.val‖ ≤ s * P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ)) *
      (∏ j ∈ T, Ms j ^ (-(1 / 18 : ℝ))) *
      (4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) *
        ((6 * C₀ : ℕ) : ℝ) ^ n * ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))))

/-- **The D7 input** (`MarkedPieceSelTargetG` composed with the class sum, per-tree form): under `1 ≤ d`, `PieceSmall`
and the three marked gates, the selected class sum holds for every uniform extra `X`. -/
def SelSumTargetTG : Prop :=
  ∀ (cP cθ : ℝ), 0 ≤ cP → 1 ≤ cθ → ∀ P : WTParams, 1 ≤ P.d → PieceSmall P →
    CoarseSplicedAtMK P → FineSplicedAtMKG P → LadderFourierAtMKFace P → ∀ X : ℝ, MarkedSumBoundSelAtTG cP cθ X P

/-- **`Stage1ReductionAtMKFullG`** (ruling R177; the gate C5b consumes): the marked Stage-1′ gate at coset base `0`,
with the weight data explicit, the plain-pattern hypothesis on selected trees, `SoundMKFullG … cθ`, and residual
selected vertices `selR π` (at most one per tree, in selected trees, unpinned, filter `(Rs j, chiDN)` — the
normalized `chiD / chiDNorm`, ruling R179 —, at most `nProt` of them) with `RepresentsIntMKSelG` at the mass `selMassMK`.
Ruling R185 (F-B3s-8): `J.card = R` after the cap set, as in `MarkedComponentBoundAtI`. Ruling R187
(LB-RESTORE-2): the residual selected vertices carry no lower bound (`(S.piece π).lb v = none`), as D7 needs. -/
def Stage1ReductionAtMKFullG (C₀ : ℕ) (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))), J.card = R → ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∃ (S : Stage1DataMKG P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (selR : ∀ π, Finset (GBranch (S.piece π).Gsb.tree)),
    Stage1Partition roots A members cls sel ∧
    (∀ π, S.val π = ∑ LG ∈ members (cls π),
        kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
          (fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k)
          (fun _ => t) 0 roots (sel π LG) ∧
      RepresentsIntMKSelG (S.piece π) (selR π) N cP (fun _ => t) 0 roots
        (selMassMK N b Rs kSel ((selR π).image fun v => v.1.1)) (S.val π) ∧
      (∃ LG ∈ members (cls π), (S.piece π).nProt ≤ (protI LG J pat t s kSel).card) ∧
      (∀ v ∈ selR π, (kSel v.1.1).isSome ∧ (S.piece π).fix v = none ∧
        ∃ ψ : SchwartzMap ℝ ℂ, (S.piece π).filt v = some (Rs v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) ∧
      (∀ v ∈ selR π, ∀ v' ∈ selR π, v.1.1 = v'.1.1 → v = v') ∧ (∀ v ∈ selR π, (S.piece π).lb v = none) ∧
      (selR π).card ≤ (S.piece π).nProt) ∧
    (∀ π, SoundMKFullG (S.piece π) p 0 roots cθ) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Fama.Stage1CountsG C₀ P R N S.toData Cl hCl cls

/-- **`Stage1ReductionAtMKSelG`** (B4's output gate; the local statement of ruling R177's
`Stage1ReductionAtMKFullG`, until B4 writes it in `MkDefs/Stage1MK.lean`): `MkDefs.Stage1ReductionAtMK` with
- `base = 0` (R177 (1), B4 finding F-B4-1: the consumer `compValue` uses `k₀ = 0`);
- the nProt clause at one member, `∃ LG ∈ members (cls π), nProt ≤ |protI LG …|` (R177 (2), F-B4-2(ii));
- open time intervals `t ∈ (p, p+1)`, `s ∈ (p, t)` (ruling R180, as in `MarkedComponentBoundAtI`);
- the weight class `MarkedWeightClassI` written with its data explicit (`h, b, Rf, σ, Rs, dag`), and the
  hypothesis `hplain` (selected trees carry the plain pattern, as in `MarkedComponentBoundAtI`);
- `SoundMKFullG … cθ` in place of `SoundMK` (F-C0-3);
- residual selected vertices `selR π` (at most one per tree, in selected trees, unpinned, filter `(Rs j, chiDN)`,
  R179), with
  `RepresentsIntMKSelG` at the mass `selMass N b Rs kSel (selR π).image` in place of `RepresentsIntMK` at `b^N`
  (F-C0-15; the `R_j⁻¹` of `selWeightCap` and the absorbed selections' `R_j^{-1/18}` are in the mass);
- `J.card = R` after the cap set (ruling R185, F-B3s-8, as `MkDefs.Stage1ReductionAtMKFull`; the consumer
  `NonregComponentBoundAtI` has it);
- the residual selected vertices carry no lower bound (ruling R187, as `MkDefs.Stage1ReductionAtMKFull`; D7 needs
  it). -/
def Stage1ReductionAtMKSelG (C₀ : ℕ) (cP cθ : ℝ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))), J.card = R → ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∃ (S : Stage1DataMKG P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (selR : ∀ π, Finset (GBranch (S.piece π).Gsb.tree)),
    Stage1Partition roots A members cls sel ∧
    (∀ π, S.val π = ∑ LG ∈ members (cls π),
        kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
          (fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k)
          (fun _ => t) 0 roots (sel π LG) ∧
      RepresentsIntMKSelG (S.piece π) (selR π) N cP (fun _ => t) 0 roots
        (selMass N b Rs kSel ((selR π).image fun v => v.1.1)) (S.val π) ∧
      (∃ LG ∈ members (cls π), (S.piece π).nProt ≤ (protI LG J pat t s kSel).card) ∧
      (∀ v ∈ selR π, (kSel v.1.1).isSome ∧ (S.piece π).fix v = none ∧
        ∃ ψ : SchwartzMap ℝ ℂ, (S.piece π).filt v = some (Rs v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) ∧
      (∀ v ∈ selR π, ∀ v' ∈ selR π, v.1.1 = v'.1.1 → v = v') ∧ (∀ v ∈ selR π, (S.piece π).lb v = none)) ∧
    (∀ π, SoundMKFullG (S.piece π) p 0 roots cθ) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Fama.Stage1CountsG C₀ P R N S.toData Cl hCl cls

/-- **PLAN-L8 item I's target**: the marked Stage-1′ gate over `𝒱_γ` for `0 < γ ≤ 1/2` (main's
`WTPrefix (MkDefs.Stage1ReductionAtMKFull C₀ cP cθ)`, B4's output, in the low-half form). -/
abbrev Stage1MKGateLow (C₀ : ℕ) (cP cθ : ℝ) : Prop :=
  WTPrefix fun P => P.γ ≤ 1 / 2 → Stage1ReductionAtMKFullG C₀ cP cθ P

end WaveTurbulence.GammaLow.Flower
