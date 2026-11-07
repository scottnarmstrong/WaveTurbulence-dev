/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3State
/-! **FINALCOUNT-G3: local copy of G8's `Cls`, `FinalShape`, `FinalDec`** (from
`/home/scott/wt-scratch/finalcount-g8/Prop96Statement.lean`, sha256 in COPIED-SHA256SUMS; copied at first read
2026-11-05 00:3x UTC) so that the mapping theorem does not depend on G8's heavy imports.  Differences from the original:
the namespace (`G8Copy`), the local `crossDarts` (identical body to `MoleProp4.crossDarts`), and the single field
`oddDeg`, which is weakened (see the docstring there and HANDOFF F-ODD). -/
@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG3.G8Copy
open WaveTurbulence

/-- The darts leaving `Y` (identical to `WaveTurbulence.MoleProp4.crossDarts`). -/
def crossDarts {V D : Type*} [DecidableEq V] [Fintype D] (N : Molecule V D) (Y : Finset V) : Finset D :=
  univ.filter fun x => N.atom x ∈ Y ∧ N.atom (N.mate x) ∉ Y

/-- Classes of the atoms of the final molecule: `ε`, `α` (label `R_v`, parameter `κ_v ∈ {0,50}`), `β`. -/
inductive Cls
  | eps
  | alpha (R : ℝ) (κ : ℕ)
  | beta

namespace Cls
/-- The label `R_v` of an `α`-atom (`1` otherwise). -/
def lab : Cls → ℝ
  | alpha R _ => R
  | _ => 1
/-- The parameter `κ_v` of an `α`-atom (`0` otherwise). -/
def kap : Cls → ℕ
  | alpha _ κ => κ
  | _ => 0
def IsAlpha : Cls → Prop
  | alpha _ _ => True
  | _ => False
def IsBeta : Cls → Prop
  | beta => True
  | _ => False
def IsEps : Cls → Prop
  | eps => True
  | _ => False
end Cls

open Classical in
/-- The protected (non-`ε`) atoms: the `α`- and `β`-atoms. -/
noncomputable def nonEps {V : Type*} (atoms : Finset V) (cls : V → Cls) : Finset V :=
  atoms.filter fun v => ¬ (cls v).IsEps

open Classical in
noncomputable def alphaAtoms {V : Type*} (atoms : Finset V) (cls : V → Cls) : Finset V :=
  atoms.filter fun v => (cls v).IsAlpha

open Classical in
noncomputable def betaAtoms {V : Type*} (atoms : Finset V) (cls : V → Cls) : Finset V :=
  atoms.filter fun v => (cls v).IsBeta

open Classical in
/-- **A chain** of `α`/`β`-atoms (L1806: "all its `α`- and `β`-atoms form several disjoint chains"): a nonempty
connected set of non-`ε` atoms closed under non-`ε` adjacency. -/
def IsChainSet {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (cls : V → Cls)
    (K : Finset V) : Prop :=
  K.Nonempty ∧ K ⊆ M.atoms ∧ (∀ v ∈ K, ¬ (cls v).IsEps) ∧
    (∀ u ∈ K, ∀ v, M.Adj u v → ¬ (cls v).IsEps → v ∈ K) ∧
    ∀ u ∈ K, ∀ v ∈ K, Relation.EqvGen (fun a b => a ∈ K ∧ b ∈ K ∧ M.Adj a b) u v

/-- **Prop 9.5 (L1806), graph-theoretic conclusions**, for one component `M₀` with classes `cls`;
`odd` says that `M₀` is the odd component. -/
structure FinalShape {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) (odd : Prop) : Prop where
  nonempty : M.atoms.Nonempty
  caps : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2
  noLoop : ∀ x, M.atom x ≠ M.atom (M.mate x)
  conn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b
  degPos : ∀ a ∈ M.atoms, 1 ≤ M.deg a
  /-- the atoms of degree `1` and `2` are classified as `α`- or `β`-atoms, and no other atom is -/
  classes : ∀ a ∈ M.atoms, (M.deg a ≤ 2 ↔ ¬ (cls a).IsEps)
  /-- the atoms of degree `2` have one incoming and one outgoing bond (they are cut atoms, L1777) -/
  dir2 : ∀ a ∈ M.atoms, M.deg a = 2 → M.outdeg a = 1 ∧ M.indeg a = 1
  /-- WEAKENED (G8 original: `M.deg u = 1 ∧ M.deg w = 3`): the odd component has two distinct odd atoms of degree `1` or
  `3`, all others have degree `2` or `4`. The `(3,3)` case occurs (both odd atoms of `M_sub` are never cut). -/
  oddDeg : odd → ∃ u ∈ M.atoms, ∃ w ∈ M.atoms, u ≠ w ∧ (M.deg u = 1 ∨ M.deg u = 3) ∧ (M.deg w = 1 ∨ M.deg w = 3) ∧
    ∀ a ∈ M.atoms, a ≠ u → a ≠ w → M.deg a = 2 ∨ M.deg a = 4
  evenDeg : ¬ odd → ∀ a ∈ M.atoms, M.deg a = 2 ∨ M.deg a = 4
  /-- no triple bond -/
  noTriple : ∀ a b, M.bondsBetween a b ≤ 2
  /-- any even component has at least one `β`-atom -/
  evenBeta : ¬ odd → ∃ a ∈ M.atoms, (cls a).IsBeta
  /-- a cycle is a double bond, or has length at least `4`, or is a triangle with at most one `α`-atom -/
  cycle : (∀ a ∈ M.atoms, M.deg a = 2) →
    M.atoms.card = 2 ∨ 4 ≤ M.atoms.card ∨ (M.atoms.card = 3 ∧ (alphaAtoms M.atoms cls).card ≤ 1)
  /-- if an even `M₀` is not a cycle, every chain has two distinct `ε`-atoms at its ends -/
  chains : ¬ odd → (¬ ∀ a ∈ M.atoms, M.deg a = 2) → ∀ K, IsChainSet M cls K →
    ∃ y₁ y₂, crossDarts M K = {y₁, y₂} ∧ y₁ ≠ y₂ ∧ (cls (M.atom (M.mate y₁))).IsEps ∧
      (cls (M.atom (M.mate y₂))).IsEps ∧ M.atom (M.mate y₁) ≠ M.atom (M.mate y₂)

/-- **Prop 9.5 (L1806) and the history properties of R18, conclusions about the decoration.** -/
structure FinalDec {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
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
  vineLG : ((∃ X j₁ j₂, M.IsVine X M.atoms j₁ j₂) ∨ (M.atoms.card = 2 ∧ ∀ a ∈ M.atoms, M.deg a = 2)) → ∀ κ, Adm κ →
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


end WaveTurbulence.FinalCountG3.G8Copy
