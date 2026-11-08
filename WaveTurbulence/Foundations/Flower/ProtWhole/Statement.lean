/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs

/-! # D6b PROT-WHOLE: the statements

* `RegularComponentBoundAtI` — D0-PROT's `RegProbe.lean` text (ruling R156 F-4, R157 shape), with the carrier
  conjunction extended by `CapGeo LG J p ∧ CapPatValid LG J pat p` exactly as in `MkDefs.MarkedComponentBoundAtI`
  (ruling R163; D2b finding F-D2b-1). The regularity clause comes last.
* `RegularComponentTargetI` — for every `B ≥ 74`, under `WTPrefixP` (C5b uses `B = 18000`).
* `RegularComponentPointwiseGate` — the prefix form of `ProtDefs.RegularComponentPointwiseAt`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtWhole
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtDefs

/-- **RegularComponentBoundAtI** (ruling R156 F-4; D0-PROT `RegProbe.lean`; carrier of R163): the per-component
bound `MkDefs.MarkedComponentBoundAtI` at `R = 1` for wholly regular width-2 capped components. Differences with
`MarkedComponentBoundAtI`: `R = 1`; the carrier adds `IsRegularCouple`; no twist closure is assumed (a regular couple
has no vine). `hplain` (F-D0-8) is the same hypothesis as there. -/
def RegularComponentBoundAtI (B : ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ, R = 1 → R ≤ 2 * Pm → ∀ n : ℕ, 1 ≤ n → n ≤ P.N (p + 1) ^ 4 →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ (J : Finset (Fin (2 * R))) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  J.card = R →
  ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ) (A : Finset (LayeredGarden (2 * R))),
    (∀ LG ∈ A, MkCarries P p n LG ∧ LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧
      CapGeo LG J p ∧ CapPatValid LG J pat p ∧ ∀ h : 2 * R = 2, IsRegularCouple (h ▸ LG.garden : Garden 2)) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
  ∀ (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
    (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
  ∀ (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
    ‖∑ LG ∈ A, compValue P LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
        (fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k) t roots‖ ≤
      P.L ^ (B * P.d * (2 * R : ℕ)) * P.δ ^ (7 * P.ν * n) * b ^ n *
        ∏ j : Fin (2 * R), (if (kSel j).isSome then (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) else 1)

/-- The D6b target: for every `B ≥ 74`, under the flower prefix. -/
def RegularComponentTargetI : Prop := ∀ B : ℝ, 74 ≤ B → WTPrefixP (RegularComponentBoundAtI B)

/-- The prefix form of the pointwise per-garden statement. -/
def RegularComponentPointwiseGate : Prop := WTPrefix RegularComponentPointwiseAt

end WaveTurbulence.Flower.ProtWhole
