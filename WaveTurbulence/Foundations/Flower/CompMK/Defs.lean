/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.PieceSel
public import WaveTurbulence.Foundations.Spine.PrefixPieceSmall
public import WaveTurbulence.Foundations.Flower.MkDefs.ChiDNorm
public import WaveTurbulence.Foundations.Flower.ProtWhole.Statement

/-! # C5b COMP-MK: the statements (inputs as named hypotheses, and the non-regular part)

* (D6b input) `ProtWhole.RegularComponentBoundAtI` / `RegularComponentTargetI` (world `ProtWhole/Statement.lean`).
* (D7 input) `FinalMKDefs.MarkedSumBoundSelAtT` / `SelSumTargetT` (world `FinalMKDefs/PieceSel.lean`, D7-2; first
  stated here, finding F-C5b-1): D7's class sum with per-tree selection scales.
* `Stage1ReductionAtMKSel`: the marked Stage-1 gate that B4 outputs (findings F-C0-3, F-C0-15 and F-C5b-2; B4's world
  form `MkDefs.Stage1ReductionAtMKFull` has one more output clause, see `Top.stage1ReductionAtMKSel_of_full`):
  `MkDefs.Stage1ReductionAtMK` with the weight data explicit, `SoundMKFull`, and the residual selected vertices
  `selR` with `RepresentsIntMKSel` at the mass `selMass`.
* `NonregComponentBoundAtI`: `MarkedComponentBoundAtI` restricted to non-regular members (ruling R156). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

namespace WaveTurbulence.Flower.CompMK

/-! ## D6b: the regular width-2 components.

`RegularComponentBoundAtI` / `RegularComponentTargetI` are D6b's `ProtWhole` statements (world
`ProtWhole/Statement.lean`): D0's `RegProbe.lean` text with the carrier extended by `CapGeo ∧ CapPatValid` (R163). -/

/-! ## D7: the selected class sum with per-tree scales (finding F-C5b-1).

`MarkedSumBoundSelAtT` and `SelSumTargetT` are D7-2's `FinalMKDefs` statements (world `FinalMKDefs/PieceSel.lean`,
copied there by source from this file's earlier text; identical). -/

/-! ## B4: the marked Stage-1 gate with full soundness and residual selections (finding F-C5b-2). -/

/-- The weight mass of a piece whose residual selected trees are `U`: `b^N ∏_{kSel j ≠ none} R_j⁻¹`, times
`R_j^{-1/18}` for the selected trees whose selected vertex is NOT residual (absorbed in a protected object: D6's
`M₂^{-a/18}` in the slot mass, D0 §5 item 1). -/
def selMass {R : ℕ} (N : ℕ) (b : ℝ) (Rs : Fin (2 * R) → ℝ) (kSel : Fin (2 * R) → Option ℕ)
    (U : Finset (Fin (2 * R))) : ℝ :=
  b ^ N * ∏ j : Fin (2 * R), (if (kSel j).isSome then (Rs j)⁻¹ * (if j ∈ U then 1 else Rs j ^ (-(1 / 18 : ℝ)))
    else 1)

/-- **`Stage1ReductionAtMKSel`** (B4's output gate; the local statement of ruling R177's
`Stage1ReductionAtMKFull`, until B4 writes it in `MkDefs/Stage1MK.lean`): `MkDefs.Stage1ReductionAtMK` with
- `base = 0` (R177 (1), B4 finding F-B4-1: the consumer `compValue` uses `k₀ = 0`);
- the nProt clause at one member, `∃ LG ∈ members (cls π), nProt ≤ |protI LG …|` (R177 (2), F-B4-2(ii));
- open time intervals `t ∈ (p, p+1)`, `s ∈ (p, t)` (ruling R180, as in `MarkedComponentBoundAtI`);
- the weight class `MarkedWeightClassI` written with its data explicit (`h, b, Rf, σ, Rs, dag`), and the
  hypothesis `hplain` (selected trees carry the plain pattern, as in `MarkedComponentBoundAtI`);
- `SoundMKFull … cθ` in place of `SoundMK` (F-C0-3);
- residual selected vertices `selR π` (at most one per tree, in selected trees, unpinned, filter `(Rs j, chiDN)`,
  R179), with
  `RepresentsIntMKSel` at the mass `selMass N b Rs kSel (selR π).image` in place of `RepresentsIntMK` at `b^N`
  (F-C0-15; the `R_j⁻¹` of `selWeightCap` and the absorbed selections' `R_j^{-1/18}` are in the mass);
- `J.card = R` after the cap set (ruling R185, F-B3s-8, as `MkDefs.Stage1ReductionAtMKFull`; the consumer
  `NonregComponentBoundAtI` has it);
- the residual selected vertices carry no lower bound (ruling R187, as `MkDefs.Stage1ReductionAtMKFull`; D7 needs
  it). -/
def Stage1ReductionAtMKSel (C₀ : ℕ) (cP cθ : ℝ) (P : WTParams) : Prop :=
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
  ∃ (S : Stage1DataMK P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (selR : ∀ π, Finset (GBranch (S.piece π).Gsb.tree)),
    Stage1Partition roots A members cls sel ∧
    (∀ π, S.val π = ∑ LG ∈ members (cls π),
        kernelKgenSel P.L P.γ P.δ LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
          (fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k)
          (fun _ => t) 0 roots (sel π LG) ∧
      RepresentsIntMKSel (S.piece π) (selR π) N cP (fun _ => t) 0 roots
        (selMass N b Rs kSel ((selR π).image fun v => v.1.1)) (S.val π) ∧
      (∃ LG ∈ members (cls π), (S.piece π).nProt ≤ (protI LG J pat t s kSel).card) ∧
      (∀ v ∈ selR π, (kSel v.1.1).isSome ∧ (S.piece π).fix v = none ∧
        ∃ ψ : SchwartzMap ℝ ℂ, (S.piece π).filt v = some (Rs v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) ∧
      (∀ v ∈ selR π, ∀ v' ∈ selR π, v.1.1 = v'.1.1 → v = v') ∧ (∀ v ∈ selR π, (S.piece π).lb v = none)) ∧
    (∀ π, SoundMKFull (S.piece π) p 0 roots cθ) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1Counts C₀ P R N S.toData Cl hCl cls

/-! ## The non-regular part. -/

/-- **`NonregComponentBoundAtI`**: `MarkedComponentBoundAtI` with the non-regular carrier clause of
`Stage1ReductionAtMK` (ruling R156: width-2 regular classes go to D6). -/
def NonregComponentBoundAtI (B : ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  1 / 2 < P.γ → ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 2 * Pm → ∀ n : ℕ, 1 ≤ n → n ≤ P.N (p + 1) ^ 4 →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ (J : Finset (Fin (2 * R))) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  J.card = R →
  ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ) (A : Finset (LayeredGarden (2 * R))),
    (∀ LG ∈ A, MkCarries P p n LG ∧ LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧
      CapGeo LG J p ∧ CapPatValid LG J pat p ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2))) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
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

end WaveTurbulence.Flower.CompMK
