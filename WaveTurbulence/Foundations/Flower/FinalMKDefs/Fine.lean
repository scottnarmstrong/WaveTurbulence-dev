/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Crude
public import WaveTurbulence.Foundations.Spine.SourceLadderInputs
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedKernelST

/-! # FINALMK-DEFS / Fine (packet C4a): the pinned fine-bound statements (C0 design, SCOPE §4.3 and §4.5)

Copied by source from `scope/C0-FINALMK/probe/FinalMKProbe.lean` (sha256 `49bf9d1e…6025`, 939 lines):
- lines 664–738 (§4.3: `splicedFourierBMK`, `sourceFrequencyBoxesE`, `splicedFourierBoxSumMK`, `LadderFourierAtMK`,
  `SubproConclusionsMK`, `FineSplicedAtMK`, `FineSplicedGateHalfMK`);
- lines 857–910 (§4.5, C4's face export for D7: `extendFixFace`, `splicedTimeDomainFace`, `splicedFourierBMKFace`,
  `splicedFourierBoxSumMKFace`, `LadderFourierAtMKFace`).

Recorded in `COPIED-SHA256SUMS`. Only the namespace, open and import lines differ. The B0 vocabulary
(`SurvivorData`, `SplicedKernelDataMK`, `splicedKernelMK`) is the world's `MkDefs.Stage1MK`; `SubproSupportMK` and
`SurvChainOrder` are C1a's `FinalMKDefs.Count`; `SplicedGeomPremises` is C2's `FinalMKDefs.Crude`. -/

@[expose] public section
set_option autoImplicit false

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs

variable {w d : ℕ}

/-! ### C4: the pinned fine bound (o73 Prop 18.1 + o75 row 12 + `FinalCountAtMK`) -/

/-- The time integral `B(α)` over the free clocks, pins fixed. -/
noncomputable def splicedFourierBMK {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (α : GBranch G.tree → ℝ) : ℂ :=
  ∫ τ : {b : GBranch G.tree // fix b = none} → ℝ,
    (splicedTimeDomainFix G layer rootTime fix).indicator
      (fun t => ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I))
      (G.extendFix fix τ)

/-- Integer frequency boxes on the non-exceptional branches. -/
def sourceFrequencyBoxesE {w : ℕ} (G : Garden w) (E : Finset (GBranch G.tree)) (A : Set (GBranch G.tree → ℝ)) :
    Set ({b : GBranch G.tree // b ∉ E} → ℤ) :=
  {σ | ∃ α ∈ A, ∀ v : {b : GBranch G.tree // b ∉ E}, ⌊α v.1⌋ = σ v}

/-- o73 (18.3): exceptional frequencies `β_E` fixed (supremum outside), boxes and local suprema off `E`. -/
noncomputable def splicedFourierBoxSumMK {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (E : Finset (GBranch G.tree)) (β : GBranch G.tree → ℝ)
    (A : Set (GBranch G.tree → ℝ)) : ℝ≥0∞ :=
  ∑' σ : sourceFrequencyBoxesE G E {α | α ∈ A ∧ ∀ v ∈ E, α v = β v},
    ⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ A) (_ : ∀ v ∈ E, α v = β v)
      (_ : ∀ v : {b : GBranch G.tree // b ∉ E}, |α v.1 - σ.1 v| ≤ 1),
      ‖splicedFourierBMK G layer rootTime fix α‖ₑ

/-- **C4 target 1 `LadderFourierAtMK`** (o73 Prop 18.1, pins only = MK-α; faces are the MK-β extension). -/
abbrev LadderFourierAtMK (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (fix : GBranch G.tree → Option ℝ) (E : Finset (GBranch G.tree))
    (scales : Finset (GBranch G.tree) → ℝ),
    (∀ v, D.layer v ≤ p) → SplicedAmplitudeBounds G D →
    (∀ b, (fix b).isSome → b ∈ E) → (∀ b t, fix b = some t → (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (β : GBranch G.tree → ℝ),
    splicedFourierBoxSumMK G D.layer D.rootTime fix E β
        (splicedFrequencySpectrum G D scales P.L P.γ P.η P.δ base roots) ≤
      ENNReal.ofReal ((((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
        (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order * P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) *
          ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S))

/-- Main's `SubproConclusions` with survivors (the per-piece input of the fine bound). -/
structure SubproConclusionsMK {R : ℕ} (G : Garden (2 * R)) (D : SplicedKernelData G d) (Cs : SubproChoices G)
    (S : SurvivorData G) (L γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) : Prop where
  structural : Cs.Structural
  survivors : S.Structural Cs
  chainOrder : SurvChainOrder S
  hinges : D.hinges = Cs.hinges
  support : ∀ z : GenDecoration G d roots 0,
    splicedEpsilon G D.hinges z.1 ≠ 0 → splicedGapIndicator G D L γ η base z.1 ≠ 0 →
    SubproSupportMK G Cs S L γ η base (univ.image (fun i => base + latticePoint L (roots i))) (bondIndex G z.1)
  hingeOutsideFirst : ∀ v ∈ Cs.hinges, ∀ i, ¬ (Cs.collection i).IsInterior v
  tripleDesignated : Cs.TripleDesignated
  hingeNoLoop : Cs.HingeNoLoop

/-- **C4 target 2 `FineSplicedAtMK`** (o75 (finalsbest2′) + o73 Thm 7.3′(3)): main's fine bound for the marked kernel,
extra `L^{2 N_E}` (C1) and `((N+1)L)^{(5d+4)|E|}` (Prop 18.1 and row 12 via FL-FIBER). Filters and indicators are
weights of modulus `≤ 1` in the absolute count (S Lemma 9.4). Ruling R187 (LB-RESTORE-2): the lower-bounded atoms
are exceptional, `(∀ b, (D.lb b).isSome → b ∈ E)` (the consumer's `E = Π_sb` contains them by `SoundMKFull.lb_prot`). -/
abbrev FineSplicedAtMK (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelDataMK G P.d) (Cs : SubproChoices G) (S : SurvivorData G) (E : Finset (GBranch G.tree)),
    SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ v, D.layer v ≤ p) →
    (∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) → (∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1) →
    (∀ b, (D.fix b).isSome → b ∈ E) → (∀ b t, D.fix b = some t → (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1) →
    (∀ b, (D.lb b).isSome → b ∈ E) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SplicedGeomPremises G → SubproConclusionsMK G D.toSplicedKernelData Cs S P.L P.γ P.η base roots →
    ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order * P.L ^ (2 * (S.m : ℝ)) *
        (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))

/-- **The C4 deliverable** (from `FinalCountGateHalfMK`, `WTPrefix LadderFourierAtMK`, FL-FIBER and the copy-threaded
cover chain). -/
abbrev FineSplicedGateHalfMK : Prop := WTPrefix fun P => 1 / 2 < P.γ → FineSplicedAtMK P

/-! C4's face export (for D7: FL-FACE's faces are o73 Prop 18.1's endpoint substitutions). -/

/-- Times with pins and endpoint substitutions: `t_b = r` if `fix b = some r`; `t_b = t_u` if `face b = some u`. -/
noncomputable def extendFixFace {w : ℕ} (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (face : GBranch G.tree → Option (GBranch G.tree))
    (τ : {b : GBranch G.tree // fix b = none ∧ face b = none} → ℝ) (b : GBranch G.tree) : ℝ :=
  match fix b, face b with
  | some r, _ => r
  | none, none => if h : fix b = none ∧ face b = none then τ ⟨b, h⟩ else 0
  | none, some u => if h : fix u = none ∧ face u = none then τ ⟨u, h⟩ else 0

/-- The layered domain on a face: box and root-time constraints for the integrated clocks; the parent/child order for
every pair with a free member, except the substituted pair (o73 §18: "the designated strict inequality removed"). -/
def splicedTimeDomainFace {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree)) :
    Set (GBranch G.tree → ℝ) :=
  {t | (∀ v, fix v = none → face v = none → t v ∈ Icc (layer v : ℝ) (layer v + 1) ∧ t v < rootTime v.1.1) ∧
    ∀ v u, v.IsChildOf u → (fix v = none ∨ fix u = none) → face v ≠ some u → face u ≠ some v → t v < t u}

noncomputable def splicedFourierBMKFace {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree)) (α : GBranch G.tree → ℝ) : ℂ :=
  ∫ τ : {b : GBranch G.tree // fix b = none ∧ face b = none} → ℝ,
    (splicedTimeDomainFace G layer rootTime fix face).indicator
      (fun t => ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I))
      (extendFixFace G fix face τ)

noncomputable def splicedFourierBoxSumMKFace {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ)
    (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (E : Finset (GBranch G.tree)) (β : GBranch G.tree → ℝ) (A : Set (GBranch G.tree → ℝ)) : ℝ≥0∞ :=
  ∑' σ : sourceFrequencyBoxesE G E {α | α ∈ A ∧ ∀ v ∈ E, α v = β v},
    ⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ A) (_ : ∀ v ∈ E, α v = β v)
      (_ : ∀ v : {b : GBranch G.tree // b ∉ E}, |α v.1 - σ.1 v| ≤ 1),
      ‖splicedFourierBMKFace G layer rootTime fix face α‖ₑ

/-- **C4 face export `LadderFourierAtMKFace`** (o73 Prop 18.1 in full: pins and at most one endpoint substitution per
tree, recipient its parent or a child; substituted atoms and their recipients exceptional). For D7 (MK-δ); the
pins-only `LadderFourierAtMK` is its `face ≡ none` case. -/
abbrev LadderFourierAtMKFace (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelData G P.d) (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (E : Finset (GBranch G.tree)) (scales : Finset (GBranch G.tree) → ℝ),
    (∀ v, D.layer v ≤ p) → SplicedAmplitudeBounds G D →
    (∀ b, (fix b).isSome → b ∈ E) → (∀ b t, fix b = some t → (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1) →
    (∀ v u, face v = some u → v ∈ E ∧ u ∈ E ∧ fix v = none ∧ fix u = none ∧ face u = none ∧
      (v.IsChildOf u ∨ u.IsChildOf v)) →
    (∀ v v', (face v).isSome → (face v').isSome → v.1.1 = v'.1.1 → v = v') →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (β : GBranch G.tree → ℝ),
    splicedFourierBoxSumMKFace G D.layer D.rootTime fix face E β
        (splicedFrequencySpectrum G D scales P.L P.γ P.η P.δ base roots) ≤
      ENNReal.ofReal ((((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) *
        (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order * P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) *
          ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S))

end WaveTurbulence.Flower.FinalMKDefs
