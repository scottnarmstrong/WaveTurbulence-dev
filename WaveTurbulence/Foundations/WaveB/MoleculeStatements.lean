/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.Molecules

/-!
# The held-out molecule definitions of the Wave B tier-B2 statements draft

Non-frozen. Text of the universe copy `WaveB2Draft/Statements.lean` (the B2-final text) without its module doc, without
the four definitions the freeze holds (`timeBox`, `timeBoxGt`, `InputRemainder`, `regBound`; ruling D8,
through `FrozenB2`) and without the sorry'd anchors (`regularAsymptotics`, `incoherentDecay`,
`rigidity`). What remains, verbatim and in order, are the twelve molecule-side definitions of the
abstract B2.3 `rigidity` statement: `AtomLabel.IsAlpha`, `Molecule.IsConnected`, `Molecule.IsPerfect`,
`Molecule.ABLinked`, `Molecule.FinalShape`, `Molecule.IsTame`, `Molecule.DecorationHyp`,
`Molecule.numBeta`, `Molecule.perfectIndicator`, `Molecule.epsDefect`, `alphaFactor`,
`Molecule.rigidityRHS`.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-! ## B2.3 `rigidity` (abstract form; design item) -/

/-- An α-label. -/
def AtomLabel.IsAlpha (a : AtomLabel) : Prop := ∃ Q κ, a = .alpha Q κ

namespace Molecule

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The molecule is connected. -/
def IsConnected : Prop := ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v

/-- **Perfect** (T Prop `finalmol`): every α- and β-atom has degree 2 and every ε-atom degree 4. -/
def IsPerfect (lab : V → AtomLabel) : Prop :=
  ∀ v ∈ M.atoms, (lab v = .eps → M.deg v = 4) ∧ (lab v ≠ .eps → M.deg v = 2)

/-- Two α/β atoms are linked through α/β atoms. -/
def ABLinked (lab : V → AtomLabel) (u v : V) : Prop :=
  Relation.EqvGen (fun a b => lab a ≠ .eps ∧ lab b ≠ .eps ∧ M.Adj a b) u v

/-- **The structural conclusions of T Prop `finalmol`** for one component of `𝕄_fin`: a connected
molecule without triple bonds whose α- and β-atoms have degree `≤ 2`; if perfect, it has a β-atom; a
perfect cycle is a double bond, a cycle of length `≥ 4`, or a triangle with at most one α-atom; in a
perfect non-cycle the α/β-atoms form chains whose two ends are joined to two distinct ε-atoms. -/
structure FinalShape (lab : V → AtomLabel) : Prop where
  molecule : M.IsMolecule
  connected : M.IsConnected
  noTriple : ∀ a b, M.bondsBetween a b ≤ 2
  abDeg : ∀ v ∈ M.atoms, lab v ≠ .eps → M.deg v ≤ 2
  perfectBeta : M.IsPerfect lab → ∃ v ∈ M.atoms, lab v = .beta
  cycle : M.IsPerfect lab → (∀ v ∈ M.atoms, M.deg v = 2) →
    M.atoms.card = 2 ∨ 4 ≤ M.atoms.card ∨
      (M.atoms.card = 3 ∧ ∀ u ∈ M.atoms, ∀ v ∈ M.atoms, (lab u).IsAlpha → (lab v).IsAlpha → u = v)
  chains : M.IsPerfect lab → ¬ (∀ v ∈ M.atoms, M.deg v = 2) → ∀ v ∈ M.atoms, lab v ≠ .eps →
    ∃ e₁ ∈ M.atoms, ∃ e₂ ∈ M.atoms, e₁ ≠ e₂ ∧ lab e₁ = .eps ∧ lab e₂ = .eps ∧
      ∀ e ∈ M.atoms, lab e = .eps →
        ((∃ u, M.ABLinked lab v u ∧ M.Adj u e) ↔ (e = e₁ ∨ e = e₂))

/-- **Tame** (T Prop `subpro` (3), L2044): in the decoration `κ`, all bonds at `v` carry the same vector, and
if `d(v) < 4` that vector is one of the fixed vectors `kFix` (T: the root momenta `(k₁, …, k_{2R})`). A
self-loop at `v` is one bond; its two darts carry the same vector (`IsDecoration`). B2-CL-15 (FINDINGS F66). -/
def IsTame {d : ℕ} (L : ℝ) (w : Mom d) (kFix : Finset (Mom d)) (κ : D → (Fin d → ℤ)) (v : V) : Prop :=
  (∀ x₁ x₂, M.atom x₁ = v → M.atom x₂ = v → kvec L w κ x₁ = kvec L w κ x₂) ∧
    (M.deg v < 4 → ∀ x, M.atom x = v → kvec L w κ x ∈ kFix)

/-- **The decoration properties guaranteed by the cutting process** (T Props `finalmol`,
`excessprop1`, Remarks `remiota`, `remtame`; WAVE-B §4.13 (ii)), for every admissible decoration `κ`
(coset `w + ℤ_L^d`). A *triple* `(v, ℓ₁, ℓ₂)` is given by darts `x₁, x₂` at `v` of opposite directions on
**two bonds**, `x₂ ≠ mate x₁` (T Def `defdiff`, L1938–L1941; a self-loop at `v` is one bond and gives no
triple; B2-CL-14, FINDINGS F66):
* every ε-atom is LG, or ZG and tame (T Prop `finalmol`, L2183–L2184: "must be LG or ZG, and must be tame if
  it is ZG"; B2-CL-15): either every triple at it has a large gap, or it is `IsTame` (then every triple at
  it has zero gap);
* every α-atom `v` is labelled `Q_v ∈ [L^{-1}, L^{-γ+η}]`, `κ_v ∈ {0, 50}`; if it has two bonds, their gap
  satisfies `Q_v ≤ |r| ≤ 2Q_v` (dyadic `∼₀`), and if `κ_v = 0` no earlier cut gap `r' ∈ prevGaps v κ`
  has `0 < |r ± r'| ≤ L^{-50η} Q_v` (`ι_v = 0`, T Remark `remiota`);
* no α- or β-atom with two bonds has zero gap;
* every maximal ladder has gap scale `P(𝕃) ∈ {0} ∪ [L^{-1}, 1]` and its gap is `0`, `∼ P`, or `≳ 1`
  according as `P = 0`, `0 < P < 1`, `P = 1`;
* if the molecule is a vine whose joints have degree 2, its gap is LG. -/
structure DecorationHyp {d : ℕ} (L γ η : ℝ) (w : Mom d) (kFix : Finset (Mom d)) (lab : V → AtomLabel)
    (prevGaps : V → (D → (Fin d → ℤ)) → Set (Mom d)) (P : Finset V → ℝ)
    (Adm : (D → (Fin d → ℤ)) → Prop) : Prop where
  epsLGTame : ∀ κ, Adm κ → ∀ v ∈ M.atoms, lab v = .eps →
    (∀ x₁ x₂, M.atom x₁ = v → M.atom x₂ = v → x₂ ≠ M.mate x₁ → M.out x₁ ≠ M.out x₂ →
      gapKind L γ η (gapAt L w κ x₁ x₂) = .LG) ∨ M.IsTame L w kFix κ v
  alphaLabel : ∀ v ∈ M.atoms, ∀ Q κv, lab v = .alpha Q κv →
    L⁻¹ ≤ Q ∧ Q ≤ L ^ (-γ + η) ∧ (κv = 0 ∨ κv = 50)
  alphaGap : ∀ κ, Adm κ → ∀ v ∈ M.atoms, ∀ Q κv, lab v = .alpha Q κv → ∀ x₁ x₂, x₁ ≠ x₂ →
    M.atom x₁ = v → M.atom x₂ = v → x₂ ≠ M.mate x₁ → M.out x₁ ≠ M.out x₂ →
    Q ≤ ‖gapAt L w κ x₁ x₂‖ ∧ ‖gapAt L w κ x₁ x₂‖ ≤ 2 * Q
  iota : ∀ κ, Adm κ → ∀ v ∈ M.atoms, ∀ Q, lab v = .alpha Q 0 → ∀ x₁ x₂, M.atom x₁ = v →
    M.atom x₂ = v → x₂ ≠ M.mate x₁ → M.out x₁ ≠ M.out x₂ → ∀ r' ∈ prevGaps v κ, ∀ s : ℝ,
    (s = 1 ∨ s = -1) →
    ¬ (0 < ‖gapAt L w κ x₁ x₂ + s • r'‖ ∧ ‖gapAt L w κ x₁ x₂ + s • r'‖ ≤ L ^ (-50 * η) * Q)
  abNonzero : ∀ κ, Adm κ → ∀ v ∈ M.atoms, lab v ≠ .eps → ∀ x₁ x₂, M.atom x₁ = v →
    M.atom x₂ = v → x₂ ≠ M.mate x₁ → M.out x₁ ≠ M.out x₂ → gapAt L w κ x₁ x₂ ≠ 0
  ladderScale : ∀ S ∈ M.maximalLadders, P S = 0 ∨ (L⁻¹ ≤ P S ∧ P S ≤ 1)
  ladderGap : ∀ κ, Adm κ → ∀ S ∈ M.maximalLadders, ∃ m : ℕ, ∃ u v : Fin (m + 1) → V,
    ∃ hm : 1 ≤ m, M.IsLadder u v ∧ ladderAtoms u v = S ∧ ∃ r, M.IsLadderGap L w κ u v hm r ∧
      (P S = 0 → r = 0) ∧ (0 < P S → P S < 1 → P S ≤ ‖r‖ ∧ ‖r‖ ≤ 2 * P S) ∧ (P S = 1 → 1 ≤ ‖r‖)
  vineLG : ∀ X j₁ j₂, M.IsVine X M.atoms j₁ j₂ → M.deg j₁ = 2 → M.deg j₂ = 2 → ∀ κ, Adm κ →
    ∀ r, M.IsBlockGap L w κ M.atoms j₁ r → gapKind L γ η r = .LG

/-- `V_β`: the number of β-atoms. -/
noncomputable def numBeta (lab : V → AtomLabel) : ℕ := by
  classical
  exact (M.atoms.filter fun v => lab v = .beta).card

/-- `G`: `1` for a perfect component, `0` otherwise. -/
noncomputable def perfectIndicator (lab : V → AtomLabel) : ℕ := by
  classical
  exact if M.IsPerfect lab then 1 else 0

/-- `Z`: `0` if `R = 1`, else the number of ε-atoms not of degree 4. -/
noncomputable def epsDefect (lab : V → AtomLabel) (Rw : ℕ) : ℕ := by
  classical
  exact if Rw = 1 then 0 else (M.atoms.filter fun v => lab v = .eps ∧ M.deg v ≠ 4).card

/-- The α-atom factor `L^{-(γ+3η)/2 + κ_v η} Q_v^{-1}` (`1` at other atoms). -/
noncomputable def alphaFactor (L γ η : ℝ) : AtomLabel → ℝ
  | .alpha Q κv => L ^ (-(γ + 3 * η) / 2 + κv * η) * Q⁻¹
  | _ => 1

/-- **The right-hand side of (finalcount)** (T Prop `lgmolect`):
`∏_{α} L^{-(γ+3η)/2+κ_vη} Q_v^{-1} · L^{(γ₀+2η²)V_β - (2γ₀+5η²)G} · L^{-η⁵ρ + ηZ}`. -/
noncomputable def rigidityRHS (P : WTParams) (lab : V → AtomLabel) (Rw : ℕ) : ℝ :=
  (∏ v ∈ M.atoms, alphaFactor P.L P.γ P.η (lab v)) *
    P.L ^ ((P.gamma0 + 2 * P.η ^ 2) * M.numBeta lab -
      (2 * P.gamma0 + 5 * P.η ^ 2) * M.perfectIndicator lab) *
    P.L ^ (-P.η ^ 5 * M.rho + P.η * M.epsDefect lab Rw)

end Molecule

end WaveTurbulence
