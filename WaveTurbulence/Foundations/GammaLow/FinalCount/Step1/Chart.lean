/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount4
public import WaveTurbulence.Foundations.TVine.Chart.Contract
public import WaveTurbulenceVineParam.VineParamMain
/-! # Every member of `𝒱_γ` is a charted block (L6-STEP1)

Main's Step-1 label count uses a vine only through a full chart (`VineParamContract.FullVineChart M X S a b`) and
`IsBlock` (`Step1.Charted`). This file supplies both for every member of the `γ`-dependent family `𝒱_γ` (ruling D11,
`Molecule.IsVineGamma`):

* the bad vines (I), (II) and the drawn vines (I)–(VIII) (`γ > 1/2`): main's sealed `Vine.Param.vineparam`;
* the T-vines (`γ ≤ 1/2`): L4's Theorem C (`TVine.Chart.TVineChartExists`, M4 §3.2, the piece chart: rung pairs are
  the 2-atom pieces, the core triple is the 3-atom piece, N2 Prop 1.17(b) / §2.1). A normal de-indexed chart
  (`TVine.Chart.FullChart M false`) is a drawn-indexed chart of type (III) when it has no single-bond junction pair, and
  of type (VII) when it has one (`toVineChart`): the type index of main's contract enters only through `X.IsBad`, the
  junction clause and the shape clauses of (I), (II) (L4's `Contract.lean` docstring), and all other fields are equal.

So the T-vine core is counted by DH23 A.2(3) at `γ ≤ 1/2` (main's `tripleSet_count`, all `γ`, gain `L^{-γ₀}`), and each
2-atom piece by A.2(1) (`pairSet_count`), exactly as in N2 §2.1 and M2 §3.5 (i). -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- **A de-indexed chart as a drawn-indexed chart** (the inverse of L4's `ofVineChart`): the type index `X` must
match `bad` (`X.IsBad`), the junction clause and the shape clauses of (I), (II); every other field is copied. -/
def toVineChart {M : Molecule V D} {S : Finset V} {a b : V} (X : VineType) (F : TVine.Chart.FullChart M X.IsBad S a b)
    (hI : X = .I → F.indexing.shape.m = 0) (hII : X = .II → 1 ≤ F.indexing.shape.m)
    (hJ : F.junction.isSome = decide (X = .VII)) : FullVineChart M X S a b where
  indexing := { shape := ⟨F.indexing.shape.m, hI, hII⟩, atom := F.indexing.atom, lower := F.indexing.lower }
  bond_count := F.bond_count
  junction := F.junction
  junction_type := hJ
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

/-- **A normal de-indexed chart gives a drawn-indexed chart**: type (III) without a junction pair, type (VII) with
one. -/
theorem exists_vineChart_of_normal {M : Molecule V D} {S : Finset V} {a b : V}
    (F : TVine.Chart.FullChart M false S a b) : ∃ X : VineType, Nonempty (FullVineChart M X S a b) := by
  cases hj : F.junction with
  | none =>
    exact ⟨.III, ⟨toVineChart .III F (by simp) (by simp) (by simp [hj])⟩⟩
  | some j =>
    exact ⟨.VII, ⟨toVineChart .VII F (by simp) (by simp) (by simp [hj])⟩⟩

/-- **A T-vine is a charted block**, given L4's Theorem C (`TVineChartExists`). -/
theorem charted_of_isTVine (hT : TVine.Chart.TVineChartExists) {V D : Type} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (hMol : M.IsMolecule) {S : Finset V} {a b : V} (h : M.IsTVine S a b) :
    Charted M S a b := by
  obtain ⟨F⟩ := hT V D M hMol S a b h
  exact ⟨h.1, exists_vineChart_of_normal F⟩

/-- **A drawn vine is a charted block** (main's sealed `VINEPARAM`). -/
theorem charted_of_isVine {V D : Type} [DecidableEq V] [Fintype D] {M : Molecule V D} (hMol : M.IsMolecule)
    {X : VineType} {S : Finset V} {a b : V} (h : M.IsVine X S a b) : Charted M S a b :=
  ⟨h.1, X, Vine.Param.vineparam V D M hMol X S a b h⟩

/-- **Every member of `𝒱_γ` is a charted block** (L6's carrier: `Src.IsSomeVine γ = IsVineGamma γ`), given L4's
Theorem C for the T-vines. -/
theorem charted_of_isSomeVine (hT : TVine.Chart.TVineChartExists) {V D : Type} [DecidableEq V] [Fintype D]
    [DecidableEq D] {γ : ℝ} {M : Molecule V D} (hMol : M.IsMolecule) {S : Finset V} {a b : V}
    (h : Src.IsSomeVine γ M S a b) : Charted M S a b := by
  rcases h with ⟨-, h | h | h⟩ | ⟨-, X, h⟩
  · exact charted_of_isVine hMol h
  · exact charted_of_isVine hMol h
  · exact charted_of_isTVine hT hMol h
  · exact charted_of_isVine hMol h

end WaveTurbulence.GammaLow.FinalCount.Step1
