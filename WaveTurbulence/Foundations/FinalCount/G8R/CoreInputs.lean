/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.Merge
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Step0OneStep
import Mathlib.Tactic

/-! # Prop 10.4(2)′: the counting steps of the case analysis, as named inputs

Orchestrator decision (option (c)): the counting estimates used in the cases of DH23's proof of Prop 10.4(2)
(L1965–L1977) are stated as named inputs in G6's relaxed count; the case analysis is proved from them. Each input is
one DH23 operation estimate `𝔄_pre ≲ 𝔇 · 𝔄_post` (L1770, (defdev)), stated for general molecules with the local
configuration of the operation. The post molecules are induced pieces (`piece`), erasures (`Degen.eraseAtoms`), a
bond re-insertion (`Mole.addBond`) or the merge (`mergePair`); a supremum over the scales of the post molecule is
taken (new ladder cells get their own scale, as in `ylem2`).

Size factors. Where DH23's deviation rests on DH21 Lemma 9.14 summed over a whole side of a cut (β-cut, bi-bridge), the
window of `|k_{ℓ₁}|² − |k_{ℓ₂}|²` has length `n δ⁻¹ L^{−2γ}` and DH23 bounds `n ≲ (log L)^C` (L1784, L1967). G6's
count has no size bound, so these inputs carry the factor `|𝕄| + 1` explicitly.

The inputs (DH23 source in brackets):
* `BetaCutInput` — β-cut at a cut vertex, the two sides counted separately [L1784; used at L1963];
* `BridgeSplitInput` — removal of a bridge, the two sides counted separately [L1963];
* `BiBridgeInput` — bi-bridge removal when `k_{ℓ₁} ≠ k_{ℓ₂}`, deviation `L^{γ₀}` [L1967, Lemma A.3(1)];
* `BiBridgeEqualInput` — bi-bridge replaced by one bond when `k_{ℓ₁} = k_{ℓ₂}` [L1969];
* `PairGainInput` — removal of an adjacent `(3,4)` double pair or `(3,3)` single pair with `Δχ = −3`, deviation
  `L^{−γ₀}` [L1965, Lemma A.3(4)];
* `SmallGapPairInput` — removal of a double pair with a small gap across it, deviation `L^{−γ₀+dη}` [L1975];
* `MergeInput` — merging a double pair without small gap, deviation `L^{−η/2}` [L1977, Lemma A.3(1) and LG].
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

section Defs
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The small-gap condition of case (III)** at the double bond `v₁ = v₂`: an extra bond `ℓ_i` of `v₁` and an extra
bond `ℓ_j` of `v₂` with `|k_{ℓ_i} ± k_{ℓ_j}| ≤ L^{−γ+η}`. -/
def SmallPairGap (M : Molecule V D) (v₁ v₂ : V) {d : ℕ} (L γ η : ℝ) (κ : D → (Fin d → ℤ)) : Prop :=
  ∃ x y, M.atom x = v₁ ∧ M.atom (M.mate x) ≠ v₂ ∧ M.atom y = v₂ ∧ M.atom (M.mate y) ≠ v₁ ∧
    (‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖ ≤ L ^ (-γ + η) ∨
      ‖Molecule.kvec L (0 : Mom d) κ x + Molecule.kvec L (0 : Mom d) κ y‖ ≤ L ^ (-γ + η))

/-- The decorations of the merged molecule coming from admissible decorations of `𝕄` (restriction). -/
def mergeAdm (M : Molecule V D) (v₁ v₂ : V) {d : ℕ} (Adm : (D → (Fin d → ℤ)) → Prop)
    (κ' : OffPair M v₁ v₂ → (Fin d → ℤ)) : Prop :=
  ∃ κ, Adm κ ∧ (∀ x, κ (M.mate x) = κ x) ∧ ∀ y, κ' y = κ y.val

end Defs

/-- **β-cut at a cut vertex** (DH23 L1784, used at L1963): the side `S` is attached to the rest only through two bonds
at `w`. Cutting `w` (Δχ = 0) and counting the two sides separately loses `≲ n (log L)^C`. -/
def BetaCutAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ (w : V) (S : Finset V), w ∈ M.atoms → S ⊆ M.atoms → w ∉ S →
      (crossDarts M S).card = 2 → (∀ x ∈ crossDarts M S, M.atom (M.mate x) = w) →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      (∀ a ∈ insert w S, ∀ b ∈ insert w S, (piece M (insert w S)).SameComponent a b) →
      (∀ a ∈ M.atoms \ S, ∀ b ∈ M.atoms \ S, (piece M (M.atoms \ S)).SameComponent a b) →
      ∀ P : Finset V → ℝ, (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
        AFree M d L γ δ η C1 P ≤ ENNReal.ofReal (K * Real.log L ^ B * (M.atoms.card + 1)) *
          AFreeSup (piece M (insert w S)) d L γ δ η C1 * AFreeSup (piece M (M.atoms \ S)) d L γ δ η C1

/-- The input: `BetaCutAt` for every `L ≥ R`. -/
def BetaCutInput (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    BetaCutAt.{u, v} d L γ δ η C1 K B

/-- **Removing a bridge** (DH23 L1963): the side `S` is attached to the rest by one bond. Its vector is fixed by the
conservation laws on `S` (Δχ = 0), and the two sides are counted separately. -/
def BridgeSplitAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ S : Finset V, S ⊆ M.atoms → (crossDarts M S).card = 1 →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      (∀ a ∈ S, ∀ b ∈ S, (piece M S).SameComponent a b) →
      (∀ a ∈ M.atoms \ S, ∀ b ∈ M.atoms \ S, (piece M (M.atoms \ S)).SameComponent a b) →
      ∀ P : Finset V → ℝ, (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
        AFree M d L γ δ η C1 P ≤ ENNReal.ofReal (K * Real.log L ^ B) *
          AFreeSup (piece M S) d L γ δ η C1 * AFreeSup (piece M (M.atoms \ S)) d L γ δ η C1

/-- The input: `BridgeSplitAt` for every `L ≥ R`. -/
def BridgeSplitInput (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    BridgeSplitAt.{u, v} d L γ δ η C1 K B

/-- **Removing a bi-bridge with `k_{ℓ₁} ≠ k_{ℓ₂}`** (DH23 L1967): the side `S` is attached to the rest by the two bonds
of `x₁, x₂` (opposite directions). `k_{ℓ₁} − k_{ℓ₂} ≠ 0` is fixed and `|k_{ℓ₁}|² − |k_{ℓ₂}|²` lies in a window of length
`≲ n δ⁻¹ L^{−2γ}`; Lemma A.3(1) gives the deviation `n (log L)^C L^{γ₀}` (Δχ = −1). -/
def BiBridgeAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ (S : Finset V) (x₁ x₂ : D), S ⊆ M.atoms → crossDarts M S = {x₁, x₂} → x₁ ≠ x₂ → M.out x₁ ≠ M.out x₂ →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      (∀ a ∈ S, ∀ b ∈ S, (piece M S).SameComponent a b) →
      (∀ a ∈ M.atoms \ S, ∀ b ∈ M.atoms \ S, (piece M (M.atoms \ S)).SameComponent a b) →
      ∀ P : Finset V → ℝ, (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdm M L γ η P κ ∧ κ x₁ ≠ κ x₂) →
        MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (K * Real.log L ^ B * (M.atoms.card + 1) * L ^ min γ (1 - γ)) *
            AFreeSup (piece M S) d L γ δ η C1 * AFreeSup (piece M (M.atoms \ S)) d L γ δ η C1

/-- The input: `BiBridgeAt` for every `L ≥ R`. -/
def BiBridgeInput (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    BiBridgeAt.{u, v} d L γ δ η C1 K B

/-- **Replacing a bi-bridge by one bond when `k_{ℓ₁} = k_{ℓ₂}`** (DH23 L1969): `x₁` leaves `S` at `a₁`, `x₂` enters `S`
at `a₂`; the two bonds are removed and a new bond `a₁ → a₂` carries their common vector (Δχ = 0). The side `S` with
the new bond and the other side are counted separately.

**Deviation (finalcount-g8, finding 2).** MOLEPROP4's `BiBridgeEqualAt` had no hypothesis on the cells of the post
molecule. For a closed 4-regular post (the crossed molecule) the cell-gap restriction of the new cells is unsatisfiable
for every scale function, so the statement was false. The added hypothesis says every cell of the post is `GoodCell`
(its gap is well defined); `case_bibridge` discharges it from a degree-three atom of the post. -/
def BiBridgeEqualAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ (S : Finset V) (x₁ x₂ : D), S ⊆ M.atoms → crossDarts M S = {x₁, x₂} → x₁ ≠ x₂ →
      M.out x₁ = true → M.out x₂ = false →
      (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      (∀ a ∈ M.atoms \ S, ∀ b ∈ M.atoms \ S, (piece M (M.atoms \ S)).SameComponent a b) →
      (∀ S' ∈ MoleProp.ladderCells (Mole.addBond (piece M S) (M.atom x₁) (M.atom x₂)),
        GoodCell (Mole.addBond (piece M S) (M.atom x₁) (M.atom x₂)) S') →
      ∀ P : Finset V → ℝ, (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdm M L γ η P κ ∧ κ x₁ = κ x₂) →
        MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (K * Real.log L ^ B) *
            AFreeSup (Mole.addBond (piece M S) (M.atom x₁) (M.atom x₂)) d L γ δ η C1 *
              AFreeSup (piece M (M.atoms \ S)) d L γ δ η C1

/-- The input: `BiBridgeEqualAt` for every `L ≥ R`. -/
def BiBridgeEqualInput (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    BiBridgeEqualAt.{u, v} d L γ δ η C1 K B

/-- **Removing an adjacent pair `a, b` with three lost circuits** (DH23 L1965, Lemma A.3(4)): `a` of degree 3 with
either a double bond to `b` of degree 4, or a single bond to `b` of degree 3; the rest stays connected (Δχ = −3).
Deviation `(log L)^C L^{−γ₀}`. -/
def PairGainAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ b → M.deg a = 3 →
      ((M.deg b = 4 ∧ M.bondsBetween a b = 2) ∨ (M.deg b = 3 ∧ M.bondsBetween a b = 1)) →
      (∀ p ∈ M.atoms, ∀ q ∈ M.atoms, M.SameComponent p q) →
      (∀ p ∈ (Degen.eraseAtoms M {a, b}).atoms, ∀ q ∈ (Degen.eraseAtoms M {a, b}).atoms,
        (Degen.eraseAtoms M {a, b}).SameComponent p q) →
      ∀ P : Finset V → ℝ, (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
        AFree M d L γ δ η C1 P ≤ ENNReal.ofReal (K * Real.log L ^ B * L ^ (-min γ (1 - γ))) *
          AFreeSup (Degen.eraseAtoms M {a, b}) d L γ δ η C1

/-- The input: `PairGainAt` for every `L ≥ R`. **Deviation (finding 3):** only for `γ > 1/2`, as in decision D9
(the `(3,3)` single-pair count `{(1,2,3),(1,4,5)}` of Lemma A.3(4) needs `γ > 1/2`, erratum E1). -/
def PairGainInput (d : ℕ) (γ η : ℝ) : Prop :=
  1 / 2 < γ → ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    PairGainAt.{u, v} d L γ δ η C1 K B

/-- **Removing a double pair with a small gap across it** (DH23 L1975): `v₁ = v₂` with both of degree 4, and
`SmallPairGap`; the rest stays connected (Δχ = −4). Fixing the two close vectors first gives the deviation
`(log L)^C L^{−γ₀+dη}`. -/
def SmallGapPairAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ v₁ ∈ M.atoms, ∀ v₂ ∈ M.atoms, v₁ ≠ v₂ → M.bondsBetween v₁ v₂ = 2 → M.deg v₁ = 4 → M.deg v₂ = 4 →
      (∀ p ∈ M.atoms, ∀ q ∈ M.atoms, M.SameComponent p q) →
      (∀ p ∈ (Degen.eraseAtoms M {v₁, v₂}).atoms, ∀ q ∈ (Degen.eraseAtoms M {v₁, v₂}).atoms,
        (Degen.eraseAtoms M {v₁, v₂}).SameComponent p q) →
      ∀ P : Finset V → ℝ, (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdm M L γ η P κ ∧ SmallPairGap M v₁ v₂ L γ η κ) →
        MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (K * Real.log L ^ B * L ^ (-(min γ (1 - γ) - d * η))) *
            AFreeSup (Degen.eraseAtoms M {v₁, v₂}) d L γ δ η C1

/-- The input: `SmallGapPairAt` for every `L ≥ R`; only for `γ > 1/2` (finding 3). -/
def SmallGapPairInput (d : ℕ) (γ η : ℝ) : Prop :=
  1 / 2 < γ → ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    SmallGapPairAt.{u, v} d L γ δ η C1 K B

/-- **Merging a double pair without small gap** (DH23 L1977): `v₁ = v₂` with both of degree 4 and no `SmallPairGap`.
The merged decoration is LG; the double bond is counted by Lemma A.3(1) with the LG gain at `v₁` (Δχ = −1), deviation
`(log L)^C L^{−η/2}`. The post count keeps the image of the admissibility, with its own scales.

**Deviation (finalcount-g8).** The hypothesis that every cell of the merged molecule is `GoodCell` was added (as for
`BiBridgeEqualAt`): the cell scales of the new cells through the merged atom are only defined for good cells. -/
def MergeAt (d : ℕ) (L γ δ η C1 K B : ℝ) : Prop :=
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
      (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
      ∀ v₁ v₂ (hv₁ : v₁ ∈ M.atoms), v₂ ∈ M.atoms → ∀ (hne : v₁ ≠ v₂), M.bondsBetween v₁ v₂ = 2 →
      M.deg v₁ = 4 → M.deg v₂ = 4 → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
      (∀ S' ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), GoodCell (mergePair M v₁ v₂ hv₁ hne) S') →
      ∀ P : Finset V → ℝ, (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
      ∀ Adm : (D → (Fin d → ℤ)) → Prop, (∀ κ, Adm κ → lgAdm M L γ η P κ ∧ ¬ SmallPairGap M v₁ v₂ L γ η κ) →
        MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (K * Real.log L ^ B * L ^ (-(η / 2))) *
            AFreeSupAdm (mergePair M v₁ v₂ hv₁ hne) d L γ δ C1
              (fun P' κ' => lgAdm (mergePair M v₁ v₂ hv₁ hne) L γ η P' κ' ∧ mergeAdm M v₁ v₂ Adm κ')

/-- The input: `MergeAt` for every `L ≥ R`. -/
def MergeInput (d : ℕ) (γ η : ℝ) : Prop :=
  1 / 2 < γ → 0 < η → η ≤ min γ (1 - γ) / 2 → ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    MergeAt.{u, v} d L γ δ η C1 K B

end WaveTurbulence.MoleProp4
