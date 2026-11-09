/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.XChain.V2Chain.GateTypes
public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.ProtWhole.Statement
public import WaveTurbulence.Foundations.FlowerTop.P7Late

/-! # FLOWER-LOW (packet L8): the statements for `0 < γ ≤ 1/2`

* **`LayergardenFlowerLowGate`**: the target FL-low. Its body is `V2Chain.LayergardenFlowerV3Gate`'s (the body of the
  frozen `layergardenFlower_v3`, and of its full-range successor `layergardenFlower_v4`; AUDIT-V4 §3), copied by
  source, with `1 / 2 < P.γ →` replaced by `P.γ ≤ 1 / 2 →` (γ = 1/2 is in this half). With the sealed
  `layergardenFlower_v3`, `GammaHalfDraft.wtPrefixP_of_halves layergardenFlower_v3 flowerest1_low` has exactly v4's
  type (AUDIT-V4 §8).
* The low per-component carriers, copied by source from main with the same single change:
  `MarkedComponentBoundAtILow` (`MkDefs.MarkedComponentBoundAtI`), `NonregComponentBoundAtILow`
  (`CompMK.NonregComponentBoundAtI`), `RegularComponentBoundAtILow` and `RegularComponentTargetILow`
  (`ProtWhole.RegularComponentBoundAtI`, `RegularComponentTargetI`). Their bodies are family-free (the twist closure
  `MarkedTwistClosed` acts at unmarked core vines, (I) and (II) minus (II-e), the same in both families; M3 §5.3
  Lemma 2).
* `NonregLowTarget`: the target of PLAN-L8 item F (the non-regular part).

Sources (sha256 in `COPIED-SHA256SUMS`): `XChain/V2Chain/GateTypes.lean`, `Flower/MkDefs/Stage1MK.lean`,
`Flower/CompMK/Defs.lean`, `Flower/ProtWhole/Statement.lean`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Flower
open WaveTurbulence Set

open Classical in
/-- **FL-low** (TARGET Prop `flowerest1`, L2279–L2305, deterministic core, as frozen in `layergardenFlower_v3/v4`),
for `0 < γ ≤ 1/2`: `V2Chain.LayergardenFlowerV3Gate` with `1 / 2 < P.γ →` replaced by `P.γ ≤ 1 / 2 →`. -/
abbrev LayergardenFlowerLowGate : Prop :=
  WTPrefixP fun Pm P => P.γ ≤ 1 / 2 →
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSumP P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (cut2.elim 1 fun j₂ =>
              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
        (dt : Bool), (kind = .tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N))

end WaveTurbulence.GammaLow.Flower

noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.ProtDefs

namespace WaveTurbulence.GammaLow.Flower

/-- `MkDefs.MarkedComponentBoundAtI` (the per-component target, B0 F-B0-1, rulings R156, R163, A2-R) for
`0 < γ ≤ 1/2`: the same body under `P.γ ≤ 1 / 2`. -/
def MarkedComponentBoundAtILow (B : ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 2 * Pm → ∀ n : ℕ, 1 ≤ n → n ≤ P.N (p + 1) ^ 4 →
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ (J : Finset (Fin (2 * R))) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  J.card = R →
  ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ) (A : Finset (LayeredGarden (2 * R))),
    (∀ LG ∈ A, MkCarries P p n LG ∧ LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧
      CapGeo LG J p ∧ CapPatValid LG J pat p) →
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

/-- `CompMK.NonregComponentBoundAtI` (ruling R156: width-2 regular classes go to D6) for `0 < γ ≤ 1/2`. -/
def NonregComponentBoundAtILow (B : ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 2 * Pm → ∀ n : ℕ, 1 ≤ n → n ≤ P.N (p + 1) ^ 4 →
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

/-- `ProtWhole.RegularComponentBoundAtI` (ruling R156 F-4, R163) for `0 < γ ≤ 1/2`. -/
def RegularComponentBoundAtILow (B : ℝ) (Pm : ℕ) (P : WTParams) : Prop :=
  P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D → ∀ R : ℕ, R = 1 → R ≤ 2 * Pm → ∀ n : ℕ, 1 ≤ n → n ≤ P.N (p + 1) ^ 4 →
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

/-- The D6b target for `0 < γ ≤ 1/2`: for every `B ≥ 74`, under the flower prefix. -/
def RegularComponentTargetILow : Prop := ∀ B : ℝ, 74 ≤ B → WTPrefixP (RegularComponentBoundAtILow B)

/-- PLAN-L8 item F: the non-regular part at `B = 17999` (main's `CompMK.nonregPrefix` output, low half). -/
def NonregLowTarget : Prop := WTPrefixP (NonregComponentBoundAtILow 17999)

end WaveTurbulence.GammaLow.Flower
