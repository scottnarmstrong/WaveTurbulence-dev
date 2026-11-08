/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.PieceSel
public import WaveTurbulence.Foundations.Flower.MkDefs.ChiDNorm

/-! # MK-DEFS (B4, ruling R177): the full marked Stage-1′ gate `Stage1ReductionAtMKFull`

The marked Stage-1′ gate in the form its consumer (C5b) reads (findings F-C0-3, F-C0-15, F-C5b-2, F-B4-7): C5b's
draft `CompMK.Stage1ReductionAtMKSel` (world `CompMK/Defs.lean`, 2026-11-08) with ruling R177 applied:
* the gate is stated at coset base `0` (F-B4-1: `MarkedWeightClassI`'s high-root clause reads the root label
  `latticePoint P.L (roots j)`, which is the root momentum only at base `0`; the consumer's `compValue` has `k₀ = 0`);
* the protected count is bounded at ONE member of the class (F-B4-2 (ii));
* one added output clause, `(selR π).card ≤ (S.piece π).nProt` (residual selected vertices are protected), used to
  derive the frozen `MkDefs.Stage1ReductionAtMK` (`RepresentsIntMKSel`'s `L^{7(47d+2)·#sel}` is absorbed in `cP`).

`selMassMK` is C5b's `selMass` verbatim (renamed to avoid a clash under `open … MkDefs`). Deviations: recorded in
`MkDefs/COPIED-SHA256SUMS` (R177). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.FinalMKDefs

namespace WaveTurbulence.Flower.MkDefs

/-- The weight mass of a piece whose residual selected trees are `U`: `b^N ∏_{kSel j ≠ none} R_j⁻¹`, times
`R_j^{-1/18}` for the selected trees whose selected vertex is NOT residual (absorbed in a protected object). C5b's
`selMass`, verbatim. -/
def selMassMK {R : ℕ} (N : ℕ) (b : ℝ) (Rs : Fin (2 * R) → ℝ) (kSel : Fin (2 * R) → Option ℕ)
    (U : Finset (Fin (2 * R))) : ℝ :=
  b ^ N * ∏ j : Fin (2 * R), (if (kSel j).isSome then (Rs j)⁻¹ * (if j ∈ U then 1 else Rs j ^ (-(1 / 18 : ℝ)))
    else 1)

/-- **`Stage1ReductionAtMKFull`** (ruling R177; the gate C5b consumes): the marked Stage-1′ gate at coset base `0`,
with the weight data explicit, the plain-pattern hypothesis on selected trees, `SoundMKFull … cθ`, and residual
selected vertices `selR π` (at most one per tree, in selected trees, unpinned, filter `(Rs j, chiDN)` — the
normalized `chiD / chiDNorm`, ruling R179 —, at most `nProt` of them) with `RepresentsIntMKSel` at the mass `selMassMK`.
Ruling R185 (F-B3s-8): `J.card = R` after the cap set, as in `MarkedComponentBoundAtI`. Ruling R187
(LB-RESTORE-2): the residual selected vertices carry no lower bound (`(S.piece π).lb v = none`), as D7 needs. -/
def Stage1ReductionAtMKFull (C₀ : ℕ) (cP cθ : ℝ) (P : WTParams) : Prop :=
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
        (selMassMK N b Rs kSel ((selR π).image fun v => v.1.1)) (S.val π) ∧
      (∃ LG ∈ members (cls π), (S.piece π).nProt ≤ (protI LG J pat t s kSel).card) ∧
      (∀ v ∈ selR π, (kSel v.1.1).isSome ∧ (S.piece π).fix v = none ∧
        ∃ ψ : SchwartzMap ℝ ℂ, (S.piece π).filt v = some (Rs v.1.1, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ)) ∧
      (∀ v ∈ selR π, ∀ v' ∈ selR π, v.1.1 = v'.1.1 → v = v') ∧ (∀ v ∈ selR π, (S.piece π).lb v = none) ∧
      (selR π).card ≤ (S.piece π).nProt) ∧
    (∀ π, SoundMKFull (S.piece π) p 0 roots cθ) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1Counts C₀ P R N S.toData Cl hCl cls

end WaveTurbulence.Flower.MkDefs
