/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulenceVineParam.Contract
public import WaveTurbulence.Foundations.TVine.Defs

/-!
# The family-generic full vine chart (L4 TVINE-CHART, the de-indexed contract)

Main's `VineParamContract.FullVineChart M X S a b` is indexed by a drawn vine type `X : VineType`. The type enters
only through `X.IsBad` (the slot count `n`, the core slots, `ζ_bad_nonzero`) and through `junction_type`
(`junction.isSome = decide (X = .VII)`) and the shape clauses `typeI`, `typeII`. This file removes the index
(research note M4 §4 "Lean-facing consequence", with the referee's repair R6): `X` is replaced by a Boolean
`bad` (`true` for the bad vines (I), (II), `false` for normal vines: (III)–(VIII) for `γ > 1/2`, the T-vines for
`γ ≤ 1/2`). Every field is kept, with these changes:

* `Shape bad` has only the rung count `m`; the clauses `typeI`, `typeII` concern drawn types and are dropped (a
  consumer that needs `1 ≤ m` for (II) gets it from the vine, not from the chart);
* `junction_type` is replaced by `junction_bad : bad = true → junction = none`. For normal vines the junction
  slot is determined by `rung_bonds` (the unique pair joined by one bond); for a T-vine it is the degree-6 piece of
  a pendant attached (P-a) (N3 Thm 6 (iii)), and for (VII) the exceptional pair;
* `ζ_bad_nonzero`, `uSlot` and the core fields take `bad = true` / `bad = false` instead of `X.IsBad`.

The fiber, bond, incidence, energy and origin notions are main's (`VineParamContract`), unchanged, so that main's
consumers (`VineEstS2`, the `VC*` files of `FinalCount`) port by replacing `X` with `bad`.

`ofVineChart` turns every drawn-vine chart of main into a de-indexed chart (`bad := X.IsBad`), with the same
groups. `TVineChartStatement` is the statement of Theorem C (M4 §3.2) with groups (TARGET Def `cohmol` for
T-vines: the groups are the pieces, N3 §4.2).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

/-- The de-indexed combinatorial shape: `m` paired (rung) slots; `bad` decides whether a core triple follows. -/
structure Shape (bad : Bool) where
  m : ℕ

namespace Shape

variable {bad : Bool}

/-- `n = 2m + 1` for a bad vine and `2m + 4` for a normal vine (the source slot count of `sumint`). -/
def n (A : Shape bad) : ℕ := 2 * A.m + 1 + if bad then 0 else 3

/-- The lower-joint slot. -/
def x0 (A : Shape bad) : Fin A.n := ⟨0, by unfold n; omega⟩

/-- The `t`-atom slot of pair `j`. -/
def xSlot (A : Shape bad) (j : Fin A.m) : Fin A.n := ⟨j + 1, by unfold n; omega⟩

/-- The `s`-atom slot of pair `j`. -/
def ySlot (A : Shape bad) (j : Fin A.m) : Fin A.n := ⟨A.m + 1 + j, by unfold n; omega⟩

/-- The three core slots of a normal vine. -/
def uSlot (A : Shape bad) (hn : bad = false) (j : Fin 3) : Fin A.n :=
  ⟨2 * A.m + 1 + j, by unfold n; simp only [hn, Bool.false_eq_true, ite_false]; omega⟩

/-- The de-indexed shape of a drawn shape. -/
def ofVine {X : VineType} (A : VineParamContract.Shape X) : Shape X.IsBad := ⟨A.m⟩

theorem ofVine_n {X : VineType} (A : VineParamContract.Shape X) : (ofVine A).n = A.n := rfl

end Shape

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- The actual atoms excluding the upper joint, the lower joint first, then the `t`-atoms, the `s`-atoms and (for a
normal vine) the three core atoms, in the source `sumint` slots. -/
structure Indexing (M : Molecule V D) (bad : Bool) (S : Finset V) (a b : V) where
  shape : Shape bad
  atom : Fin shape.n ≃ ↥(S.erase a)
  lower : (atom shape.x0).1 = b

/-- The resonance at slot `i`: the internal energy of its atom, plus `|g|² − |g − r|²` at the lower joint. -/
noncomputable def nodeResonance {d : ℕ} {M : Molecule V D} {bad : Bool} {S : Finset V} {a b : V}
    (A : Indexing M bad S a b) (k : Bond M S → Mom d) (g r : Mom d) (i : Fin A.shape.n) : ℝ :=
  energy M S k (A.atom i).1 + if i = A.shape.x0 then ‖g‖ ^ 2 - ‖g - r‖ ^ 2 else 0

/-- **The family-generic full vine chart** (de-indexed `FullVineChart`). All fields are molecule-level coordinates
or exact normal forms of the source parametrization (TARGET Prop `sumint` (i)–(iii), phase normal form). -/
structure FullChart (M : Molecule V D) (bad : Bool) (S : Finset V) (a b : V) where
  indexing : Indexing M bad S a b
  bond_count : (internalBondSet M S).card = 2 * indexing.shape.n
  /-- The paired slot joined by a single bond, if any; every other pair is a doubled rung. -/
  junction : Option (Fin indexing.shape.m)
  junction_bad : bad = true → junction = none
  rung_bonds : ∀ j : Fin indexing.shape.m,
    M.bondsBetween (indexing.atom (indexing.shape.xSlot j)).1
      (indexing.atom (indexing.shape.ySlot j)).1 = if junction = some j then 1 else 2
  decodeFree : Matrix (Bond M S) (Fin indexing.shape.n) ℤ
  decodeGap : Bond M S → ℤ
  free_unit : ∀ e i, UnitCoeff (decodeFree e i)
  chart : ∀ {E : Type} [AddCommGroup E] (_g r : E),
    FlowFiber M S a b E r ≃ (Fin indexing.shape.n → E)
  decode_eq : ∀ {E : Type} [AddCommGroup E] (g r : E) (x : Fin indexing.shape.n → E) (e : Bond M S),
    ((chart g r).symm x).1 e = g + (∑ i, decodeFree e i • x i) + decodeGap e • r
  difference : ∀ i, ∃ p q : Bond M S ⊕ Fin 2,
    ∀ {E : Type} [AddCommGroup E] (g r : E) (k : FlowFiber M S a b E r),
      chart g r k i = origin M S k.1 g r p - origin M S k.1 g r q
  ζc : Fin indexing.shape.m → Fin 3 → ℤ
  ζ_unit : ∀ j c, UnitCoeff (ζc j c)
  ζ_bad_nonzero : bad = true → ∀ j, ζc j 0 ≠ 0 ∨ ζc j 1 ≠ 0
  coreLinear : Bool
  coreFirstSign : ℤˣ
  coreSign : ℤˣ
  ξc : Fin 4 → ℤ
  ξ_unit : ∀ c, UnitCoeff (ξc c)
  joint_phase : ∀ (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d),
    nodeResonance indexing ((chart g r).symm x).1 g r indexing.shape.x0 =
      2 * inner ℝ r (x indexing.shape.x0)
  rung_t_phase : ∀ (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d) (j : Fin indexing.shape.m),
    nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.xSlot j) =
      2 * inner ℝ (x (indexing.shape.xSlot j)) (x (indexing.shape.ySlot j)) +
        2 * inner ℝ r ((ζc j 0 : ℝ) • x (indexing.shape.xSlot j) +
          (ζc j 1 : ℝ) • x (indexing.shape.ySlot j) + (ζc j 2 : ℝ) • r)
  rung_s_phase : ∀ (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d) (j : Fin indexing.shape.m),
    nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.ySlot j) =
      -2 * inner ℝ (x (indexing.shape.xSlot j)) (x (indexing.shape.ySlot j))
  core_first_phase : ∀ (hn : bad = false) (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d),
    nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.uSlot hn 0) =
      2 * ((coreFirstSign : ℤ) : ℝ) * inner ℝ (x (indexing.shape.uSlot hn 0)) (x (indexing.shape.uSlot hn 1))
  core_second_phase : ∀ (hn : bad = false) (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d),
    nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.uSlot hn 1) =
      2 * ((coreFirstSign : ℤ) : ℝ) * (if coreLinear then
          inner ℝ (x (indexing.shape.uSlot hn 0)) (x (indexing.shape.uSlot hn 2))
        else ((coreSign : ℤ) : ℝ) * inner ℝ (x (indexing.shape.uSlot hn 2))
          (x (indexing.shape.uSlot hn 0) + x (indexing.shape.uSlot hn 1) - x (indexing.shape.uSlot hn 2)))
  core_sum_phase : ∀ (hn : bad = false) (d : ℕ) (g r : Mom d) (x : Fin indexing.shape.n → Mom d),
    (∑ c : Fin 3, nodeResonance indexing ((chart g r).symm x).1 g r (indexing.shape.uSlot hn c)) =
      2 * inner ℝ r ((ξc 0 : ℝ) • x (indexing.shape.uSlot hn 0) +
        (ξc 1 : ℝ) • x (indexing.shape.uSlot hn 1) +
        (ξc 2 : ℝ) • x (indexing.shape.uSlot hn 2) + (ξc 3 : ℝ) • r)

/-! ## Groups of a chart -/

/-- The groups of a chart: its paired slots and (for a normal vine) its core triple, as sets of actual atoms. -/
noncomputable def chartGroups {M : Molecule V D} {bad : Bool} {S : Finset V} {a b : V}
    (F : FullChart M bad S a b) : Finset (Finset V) := by
  classical
  exact (univ.image fun j : Fin F.indexing.shape.m =>
      ({(F.indexing.atom (F.indexing.shape.xSlot j)).1, (F.indexing.atom (F.indexing.shape.ySlot j)).1} :
        Finset V)) ∪
    if hn : bad = false then
      {{(F.indexing.atom (F.indexing.shape.uSlot hn 0)).1, (F.indexing.atom (F.indexing.shape.uSlot hn 1)).1,
        (F.indexing.atom (F.indexing.shape.uSlot hn 2)).1}}
    else ∅

/-! ## Drawn-vine charts are de-indexed charts -/

/-- The de-indexed indexing of a drawn-vine indexing (the same atom map). -/
def Indexing.ofVine {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (A : VineParamContract.Indexing M X S a b) : Indexing M X.IsBad S a b where
  shape := Shape.ofVine A.shape
  atom := A.atom
  lower := A.lower

theorem nodeResonance_ofVine {d : ℕ} {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (A : VineParamContract.Indexing M X S a b) (k : Bond M S → Mom d) (g r : Mom d) (i : Fin A.shape.n) :
    nodeResonance (Indexing.ofVine A) k g r i = VineParamContract.nodeResonance A k g r i := rfl

/-- **Every drawn-vine chart of main is a de-indexed chart** (`bad := X.IsBad`). -/
def ofVineChart {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (F : FullVineChart M X S a b) : FullChart M X.IsBad S a b where
  indexing := Indexing.ofVine F.indexing
  bond_count := F.bond_count
  junction := F.junction
  junction_bad := by
    intro h
    have hj := F.junction_type
    show F.junction = none
    cases hJ : F.junction with
    | none => rfl
    | some j =>
      exfalso
      rw [hJ] at hj
      simp only [Option.isSome_some] at hj
      have hX : X = .VII := of_decide_eq_true hj.symm
      subst hX
      simp [VineType.IsBad] at h
  rung_bonds := F.rung_bonds
  decodeFree := F.decodeFree
  decodeGap := F.decodeGap
  free_unit := F.free_unit
  chart := F.chart
  decode_eq := F.decode_eq
  difference := F.difference
  ζc := F.ζc
  ζ_unit := F.ζ_unit
  ζ_bad_nonzero := F.ζ_bad_nonzero
  coreLinear := F.coreLinear
  coreFirstSign := F.coreFirstSign
  coreSign := F.coreSign
  ξc := F.ξc
  ξ_unit := F.ξ_unit
  joint_phase := F.joint_phase
  rung_t_phase := F.rung_t_phase
  rung_s_phase := F.rung_s_phase
  core_first_phase := F.core_first_phase
  core_second_phase := F.core_second_phase
  core_sum_phase := F.core_sum_phase

theorem ofVineChart_atom {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (F : FullVineChart M X S a b) (i : Fin F.indexing.shape.n) :
    ((ofVineChart F).indexing.atom i).1 = (F.indexing.atom i).1 := rfl

/-! ## The chart statements -/

/-- **Theorem C** (M4 §3.2, the piece chart; with the referee's repair R1), with groups: every T-vine, with
either joint as the upper joint `a`, has a normal de-indexed full chart whose paired slots and core triple are
exactly its pieces (the T-vine groups, N3 §4.2; pinned `Molecule.tvineGroups`). -/
def TVineChartStatement : Prop :=
  ∀ (V D : Type) [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    ∀ (S : Finset V) (a b : V), M.IsTVine S a b →
      ∃ F : FullChart M false S a b, chartGroups F = M.tvineGroups S a b

/-- The chart statement without groups (what the parametrization alone needs). -/
def TVineChartExists : Prop :=
  ∀ (V D : Type) [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    ∀ (S : Finset V) (a b : V), M.IsTVine S a b → Nonempty (FullChart M false S a b)

theorem TVineChartStatement.exists (h : TVineChartStatement) : TVineChartExists := by
  intro V D _ _ _ M hM S a b hT
  obtain ⟨F, -⟩ := h V D M hM S a b hT
  exact ⟨F⟩

/-- **The family-generic chart contract for `𝒱_γ`** (PLAN §3 row L4): every member of the `γ`-dependent vine
family has a de-indexed full chart, bad for the bad vines (I), (II) and normal otherwise. -/
def VineGammaChartStatement : Prop :=
  ∀ (γ : ℝ) (V D : Type) [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    ∀ (S : Finset V) (a b : V), M.IsVineGamma γ S a b →
      (M.IsBadVine S a b → Nonempty (FullChart M true S a b)) ∧
        (¬ M.IsBadVine S a b → Nonempty (FullChart M false S a b))

end WaveTurbulence.TVine.Chart
