/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.EvenCase96
public import WaveTurbulence.Foundations.GammaLow.FinalCount.NamedInputs
import Mathlib.Tactic

/-! # DH23 Proposition 9.6 at `0 < γ ≤ 1/2`: the statement (packet L6, item F; M2 §4.0, §9)

* `FinalDecLow`: main's `FinalDec` with `vineLG` over `𝒱_γ` (M2 §9 `FinalDecLow`).
* `Prop96LowAt d γ η`: main's `Prop96At` with `FinalDecLow` (M2 §9 `Prop96LowAt`; hypotheses `hsm`, `hηs`, no `hsm2`).
* `EvenCaseLowAt`: main's `EvenCaseAt` with `FinalDecLow` (the shape of case (4)′, which uses `vineLG` on a T-vine).
* NAMED INPUT `DrawnTVineInput` (N2 Lemma 5.2, `research-gamma-half-2/NOTES.md` L828–L837, REFEREED REF2 item
  "Lemma 5.2 holds for every orientation up to 21 atoms"; owner L3): every vine of a drawn type (III)–(VIII) is a
  T-vine. With it, `FinalDecLow → FinalDec` at `γ ≤ 1/2` (`finalDec_of_low`), so main's `FinalDec`-based case lemmas
  apply. -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp4

/-- **Prop 9.5′ (L1806 with `𝒱_γ`), conclusions about the decoration** (M2 §4.0 `FinalDec_γ`): main's `FinalDec` with
`vineLG` read over the family `𝒱_γ` (`Molecule.IsVineGamma γ`, ruling D11) instead of the drawn vines (I)–(VIII). -/
structure FinalDecLow {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) {d : ℕ} (L γ η : ℝ) (Adm : (D → (Fin d → ℤ)) → Prop) : Prop where
  /-- the labels of `α`-atoms lie in `[L⁻¹, L^{-γ+η}]`, `κ_v ∈ {0, 50}` -/
  labRange : ∀ a ∈ M.atoms, (cls a).IsAlpha → L⁻¹ ≤ (cls a).lab ∧ (cls a).lab ≤ L ^ (-γ + η)
  kapVals : ∀ a ∈ M.atoms, (cls a).IsAlpha → (cls a).kap = 0 ∨ (cls a).kap = 50
  /-- each `ε`-atom is LG in the decoration -/
  epsLG : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsEps →
    ∀ x y, M.atom x = a → M.atom y = a → M.out x ≠ M.out y →
      L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖
  /-- `|k_{ℓ₁} - k_{ℓ₂}| ∼ R_v` at an `α`-atom with two bonds -/
  alphaGap : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsAlpha → ∀ x y, M.atom x = a → M.atom y = a → x ≠ y →
    (cls a).lab / 2 ≤ ‖Molecule.gapAt L (0 : Mom d) κ x y‖ ∧ ‖Molecule.gapAt L (0 : Mom d) κ x y‖ ≤ 2 * (cls a).lab
  /-- an `α`-atom is an SG atom: its gap is not large (`≤ L^{-γ+η}`, DH23 Def 8.3; LG is the strict complement `>`) -/
  alphaSG : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsAlpha → ∀ x y, M.atom x = a → M.atom y = a → x ≠ y →
    ‖Molecule.gapAt L (0 : Mom d) κ x y‖ ≤ L ^ (-γ + η)
  /-- (N1) every `β`-atom has a nonzero gap (L1874) -/
  betaGap : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsBeta → ∀ x y, M.atom x = a → M.atom y = a → x ≠ y →
    Molecule.gapAt L (0 : Mom d) κ x y ≠ 0
  /-- a vine component (two joints of degree `2`) is LG in the decoration; a double bond is vine (I) (L1806, second
  sentence of the cycle clause), included as the second disjunct -/
  vineLG : ((∃ j₁ j₂, M.IsVineGamma γ M.atoms j₁ j₂) ∨ (M.atoms.card = 2 ∧ ∀ a ∈ M.atoms, M.deg a = 2)) → ∀ κ, Adm κ →
    ∀ x y, M.atom x = M.atom y → M.out x ≠ M.out y →
      L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖
  /-- (N3) no `β`-cut with nonzero gap (L1887, "one cannot make any `β`-cuts in `𝕄₀`"; G3's `NoBetaCut` for nonzero-gap
  cuts): every cut of a vertex of degree `≥ 3` with nonzero gap `k_{x₁}-k_{x₂}` is an `α`-cut. It depends on the
  decoration through the gap, hence lives in `FinalDec`. -/
  noBetaCut : ∀ κ, Adm κ → ∀ v ∈ M.atoms, 3 ≤ M.deg v → ∀ v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ →
    Molecule.gapAt L (0 : Mom d) κ x₁ x₂ ≠ 0 → M.IsAlphaCut v v₂ x₁ x₂
  /-- (N2) the `ι/κ` property of case (6) (L1895): two `α`-atoms `v₁ ≠ v₂` with `κ_{v₁}+κ_{v₂} = 0` and a `β`-atom `v₃`
  whose gaps `r₁, r₂, r₃` are nonzero with `±r₁ ± r₂ ± r₃ = 0` force `|r₃| ≳ L^{-50η} min(R₁,R₂)`. -/
  iota : ∀ κ, Adm κ → ∀ v₁ ∈ M.atoms, ∀ v₂ ∈ M.atoms, ∀ v₃ ∈ M.atoms, v₁ ≠ v₂ →
    (cls v₁).IsAlpha → (cls v₂).IsAlpha → (cls v₃).IsBeta → (cls v₁).kap + (cls v₂).kap = 0 →
    ∀ x₁ y₁ x₂ y₂ x₃ y₃, M.atom x₁ = v₁ → M.atom y₁ = v₁ → x₁ ≠ y₁ → M.atom x₂ = v₂ → M.atom y₂ = v₂ → x₂ ≠ y₂ →
      M.atom x₃ = v₃ → M.atom y₃ = v₃ → x₃ ≠ y₃ →
      Molecule.gapAt L (0 : Mom d) κ x₁ y₁ ≠ 0 → Molecule.gapAt L (0 : Mom d) κ x₂ y₂ ≠ 0 →
      Molecule.gapAt L (0 : Mom d) κ x₃ y₃ ≠ 0 →
      (∃ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
        Molecule.gapAt L (0 : Mom d) κ x₃ y₃ =
          s₁ • Molecule.gapAt L (0 : Mom d) κ x₁ y₁ + s₂ • Molecule.gapAt L (0 : Mom d) κ x₂ y₂) →
      L ^ (-50 * η) * min (cls v₁).lab (cls v₂).lab / 2 ≤ ‖Molecule.gapAt L (0 : Mom d) κ x₃ y₃‖

universe u v

/-- At `γ ≤ 1/2`, a drawn vine is a member of `𝒱_γ` (given N2 Lemma 5.2). -/
theorem isVineGamma_of_isVine (hDT : DrawnTVineInput.{u, v}) {V : Type u} {D : Type v} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} {γ : ℝ} (hγ : γ ≤ 1 / 2) {X : VineType} {S : Finset V} {a b : V}
    (h : M.IsVine X S a b) : M.IsVineGamma γ S a b := by
  refine Or.inl ⟨hγ, ?_⟩
  cases X with
  | I => exact Or.inl h
  | II => exact Or.inr (Or.inl h)
  | _ => exact Or.inr (Or.inr (hDT M _ S a b (by intro h'; cases h') (by intro h'; cases h') h))

/-- `FinalDecLow → FinalDec` at `γ ≤ 1/2`, given N2 Lemma 5.2. -/
theorem finalDec_of_low (hDT : DrawnTVineInput.{u, v}) {V : Type u} {D : Type v} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} {cls : V → Cls} {d : ℕ} {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop}
    (hγ : γ ≤ 1 / 2) (h : FinalDecLow M cls L γ η Adm) : FinalDec M cls L γ η Adm where
  labRange := h.labRange
  kapVals := h.kapVals
  epsLG := h.epsLG
  alphaGap := h.alphaGap
  alphaSG := h.alphaSG
  betaGap := h.betaGap
  vineLG := fun hv => h.vineLG (by
    rcases hv with ⟨X, j₁, j₂, hX⟩ | h2
    · exact Or.inl ⟨j₁, j₂, isVineGamma_of_isVine hDT hγ hX⟩
    · exact Or.inr h2)
  noBetaCut := h.noBetaCut
  iota := h.iota

/-- **Proposition 9.6 at `0 < γ ≤ 1/2`** (`lgmolect` with `𝒱_γ`, DH23 L1819–L1822; M2 §4): main's `Prop96At` with
`FinalDecLow`. -/
def Prop96LowAt.{u', v'} (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, ∀ L ≥ R₀,
    ∀ {V : Type u'} {D : Type v'} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      FinalShape M cls odd → FinalDecLow M cls L γ η Adm →
      (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      (∀ S, 0 ≤ P S) →
      MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm → (∃ v₂ : V, v₂ ∉ M.atoms) →
      M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η)

/-- Main's `EvenCaseAt` with `FinalDecLow` (the shape of case (4)′). -/
def EvenCaseLowAt.{u', v'} (d : ℕ) (γ η : ℝ) (Cnd : ℕ → ℕ → Prop) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type u'} {D : Type v'} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      FinalShape M cls odd → FinalDecLow M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm →
      (∃ v₂ : V, v₂ ∉ M.atoms) → ¬ odd →
      (¬ ∀ a ∈ M.atoms, M.deg a = 2) → Cnd (alphaAtoms M.atoms cls).card (betaAtoms M.atoms cls).card →
      M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η)

end WaveTurbulence.GammaLow.FinalCount
