/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Contract
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.VineEst.VineEstS2.M9ChosenChart
public import WaveTurbulenceVineParam.VineParamGrouped

/-!
# The vine family `𝒱_γ` as consumed by the vine estimate (packet L5b, FAMILY-γ)

TARGET Prop `vineest` (L1742–L1751) estimates a vine chain through the charts of its ingredients (TARGET Prop
`sumint`, L1595: a bad vine is a unit with `n = 2m + 1` slots, a normal vine a Nor unit with `n = 2m + 4`) and through
the cohmol incoherency index of its ingredients (TARGET Def `cohmol`, L1489–L1499). For the family `𝒱_γ` of ruling D11
(`Molecule.IsVineGamma`, used through L6's carrier `FinalCount.Src.IsSomeVine γ`):

* `famGroups γ M S a b`: the groups of a member (TARGET Def `cohmol`): the drawn template groups for the bad vines
  (I), (II) (and for the drawn vines when `1/2 < γ`), the pieces `Molecule.tvineGroups` of a T-vine when `γ ≤ 1/2`
  (note 3 §4.2; PLAN row T2);
* `NormalChartSupply γ`: every normal member (`Molecule.IsNormalVineGamma`) has a de-indexed full chart (L4's
  `TVine.Chart.FullChart M false`) whose paired slots and core triple are its groups. For `γ ≤ 1/2` this is L4's
  Theorem C with groups (`TVine.Chart.TVineChartStatement`), see `normalChartSupply_of_tvine`; the bad members use
  main's sealed grouped catalogue (`Vine.Param.vineparam_grouped`).

**Chart labels.** Main's chart-generic code (`VineParamContract.FullVineChart M X`, its normalization and slot API) is
reused by import: a normal de-indexed chart is re-indexed to `FullVineChart M .III` (no junction) or `.VII` (one
junction), `toVineChartIII` / `toVineChartVII`. The index `X` of `FullVineChart` enters only through `X.IsBad` (slot
count, core slots) and `junction_type`, so for a normal chart this re-indexing is a field copy; the label carries no
claim about the vine. `LabelCharted γ M X S a b` says that `X` labels a grouped chart.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Famb

open WaveTurbulence.VineParamContract WaveTurbulence.Vine.Param

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

/-! ## Groups and the chart supply -/

open Classical in
/-- **The cohmol groups of a member of `𝒱_γ`** (TARGET Def `cohmol` with ruling D11): the drawn template groups of
the chosen realization for (I), (II) and for the drawn vines when `1/2 < γ`; the T-vine pieces when `γ ≤ 1/2`. -/
noncomputable def famGroups (γ : ℝ) (M : Molecule V D) (S : Finset V) (a b : V) : Finset (Finset V) :=
  if hI : M.IsVine .I S a b then realizedGroupSet (VineEstS2.chosenRealization hI)
  else if hII : M.IsVine .II S a b then realizedGroupSet (VineEstS2.chosenRealization hII)
  else if γ ≤ 1 / 2 then M.tvineGroups S a b
  else if h : ∃ X : VineType, M.IsVine X S a b then realizedGroupSet (VineEstS2.chosenRealization h.choose_spec)
  else ∅

/-- **The chart supply for the normal members of `𝒱_γ`** (L4's de-indexed contract with groups): every normal member
has a normal full chart whose paired slots and core triple are its cohmol groups. -/
def NormalChartSupply (γ : ℝ) : Prop :=
  ∀ (V D : Type) [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), M.IsMolecule →
    ∀ (S : Finset V) (a b : V), M.IsNormalVineGamma γ S a b →
      ∃ F : TVine.Chart.FullChart M false S a b, TVine.Chart.chartGroups F = famGroups γ M S a b

omit [Fintype D] [DecidableEq D] in
/-- **The incoherency index of a group set** (TARGET Def `cohmol`, L1489–L1499): the number of groups whose atoms do
not all lie in one layer. -/
def groupIncoherency (gs : Finset (Finset V)) (layer : V → ℕ) : ℕ :=
  (gs.filter fun g => ¬ ∀ x ∈ g, ∀ y ∈ g, layer x = layer y).card

omit [Fintype D] [DecidableEq D] in
/-- The incoherency index of a group set is main's list index `Vine.incoherencyIndex` of its groups. -/
theorem groupIncoherency_eq_incoherencyIndex (gs : Finset (Finset V)) (layer : V → ℕ) :
    groupIncoherency gs layer = Vine.incoherencyIndex layer (gs.toList.map Finset.toList) := by
  classical
  unfold groupIncoherency Vine.incoherencyIndex
  rw [List.filter_map, List.length_map]
  have hp : ∀ g : Finset V, (¬ Vine.GroupCoherent layer g.toList) ↔ ¬ ∀ x ∈ g, ∀ y ∈ g, layer x = layer y := by
    intro g; simp only [Vine.GroupCoherent, Finset.mem_toList]
  rw [Finset.card_def, Finset.filter_val, ← Multiset.coe_toList gs.val]
  rw [Multiset.filter_coe, Multiset.coe_card]
  have e : (Function.comp (fun g => decide ¬ Vine.GroupCoherent layer g) Finset.toList) =
      fun g : Finset V => decide ¬ ∀ x ∈ g, ∀ y ∈ g, layer x = layer y := by
    funext g; exact decide_eq_decide.mpr (hp g)
  rw [e]
  rfl

/-- `X` labels a full chart of `(S, a, b)` whose groups are the cohmol groups. -/
def LabelCharted (γ : ℝ) (M : Molecule V D) (X : VineType) (S : Finset V) (a b : V) : Prop :=
  ∃ F : FullVineChart M X S a b, chartAtomGroups F = famGroups γ M S a b

omit [Fintype D] in
/-- Every member of `𝒱_γ` is a block with its joints (L6's `Src.isBlock_of_isSomeVine`). -/
theorem memBlock {γ : ℝ} [Fintype D] {M : Molecule V D} {S : Finset V} {a b : V}
    (h : FinalCount.Src.IsSomeVine γ M S a b) : M.IsBlock S a b :=
  FinalCount.Src.isBlock_of_isSomeVine h

/-! ## Re-indexing a normal de-indexed chart -/

section reindex

variable {M : Molecule V D} {S : Finset V} {a b : V}

/-- A normal de-indexed chart without junction, as a full chart labelled `III` (field copy). -/
def toVineChartIII (F : TVine.Chart.FullChart M false S a b) (h : F.junction = none) :
    FullVineChart M .III S a b where
  indexing := ⟨⟨F.indexing.shape.m, (fun h => nomatch h), (fun h => nomatch h)⟩, F.indexing.atom, F.indexing.lower⟩
  bond_count := F.bond_count
  junction := F.junction
  junction_type := by rw [h]; rfl
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

/-- A normal de-indexed chart with a junction, as a full chart labelled `VII` (field copy). -/
def toVineChartVII (F : TVine.Chart.FullChart M false S a b) (h : F.junction.isSome = true) :
    FullVineChart M .VII S a b where
  indexing := ⟨⟨F.indexing.shape.m, (fun h => nomatch h), (fun h => nomatch h)⟩, F.indexing.atom, F.indexing.lower⟩
  bond_count := F.bond_count
  junction := F.junction
  junction_type := by rw [h]; rfl
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

theorem chartAtomGroups_toVineChartIII (F : TVine.Chart.FullChart M false S a b) (h : F.junction = none) :
    chartAtomGroups (toVineChartIII F h) = TVine.Chart.chartGroups F := by
  unfold chartAtomGroups shapeGroupSet TVine.Chart.chartGroups
  rfl

theorem chartAtomGroups_toVineChartVII (F : TVine.Chart.FullChart M false S a b) (h : F.junction.isSome = true) :
    chartAtomGroups (toVineChartVII F h) = TVine.Chart.chartGroups F := by
  unfold chartAtomGroups shapeGroupSet TVine.Chart.chartGroups
  rfl

omit [DecidableEq D] in
/-- The groups of a drawn chart and of its de-indexed chart agree. -/
theorem chartGroups_ofVineChart {X : VineType} (F : FullVineChart M X S a b) :
    TVine.Chart.chartGroups (TVine.Chart.ofVineChart F) = chartAtomGroups F := by
  unfold chartAtomGroups shapeGroupSet TVine.Chart.chartGroups
  rfl

/-- A normal grouped de-indexed chart gives a normal label with a grouped full chart. -/
theorem exists_label_of_chart {γ : ℝ} (F : TVine.Chart.FullChart M false S a b)
    (hF : TVine.Chart.chartGroups F = famGroups γ M S a b) :
    ∃ X : VineType, X.IsBad = false ∧ LabelCharted γ M X S a b := by
  cases hJ : F.junction with
  | none => exact ⟨.III, rfl, toVineChartIII F hJ, (chartAtomGroups_toVineChartIII F hJ).trans hF⟩
  | some j =>
    have hs : F.junction.isSome = true := by rw [hJ]; rfl
    exact ⟨.VII, rfl, toVineChartVII F hs, (chartAtomGroups_toVineChartVII F hs).trans hF⟩

end reindex

/-! ## The supply from Theorem C -/

/-- A drawn normal vine has a normal de-indexed chart with the groups of any realization (main's sealed grouped
catalogue). -/
theorem exists_normal_chart_of_drawn {M : Molecule V D} (hM : M.IsMolecule) {X : VineType} {S : Finset V}
    {a b : V} (hX : M.IsVine X S a b) (hbad : X.IsBad = false) (R : Vine.VineRealization M X S a b) :
    ∃ F : TVine.Chart.FullChart M false S a b, TVine.Chart.chartGroups F = realizedGroupSet R := by
  obtain ⟨F, hF⟩ := vineparam_grouped V D M hM X S a b hX R
  cases X with
  | I => exact absurd hbad (by decide)
  | II => exact absurd hbad (by decide)
  | III => exact ⟨TVine.Chart.ofVineChart F, (chartGroups_ofVineChart F).trans hF⟩
  | IV => exact ⟨TVine.Chart.ofVineChart F, (chartGroups_ofVineChart F).trans hF⟩
  | V => exact ⟨TVine.Chart.ofVineChart F, (chartGroups_ofVineChart F).trans hF⟩
  | VI => exact ⟨TVine.Chart.ofVineChart F, (chartGroups_ofVineChart F).trans hF⟩
  | VII => exact ⟨TVine.Chart.ofVineChart F, (chartGroups_ofVineChart F).trans hF⟩
  | VIII => exact ⟨TVine.Chart.ofVineChart F, (chartGroups_ofVineChart F).trans hF⟩

/-- A vine of type other than (I), (II) is a normal type. -/
theorem isBad_false_of_ne {X : VineType} (hI : X ≠ .I) (hII : X ≠ .II) : X.IsBad = false := by
  cases X <;> first | rfl | exact absurd rfl hI | exact absurd rfl hII

/-- **The chart supply from L4's Theorem C** (T-vines, with groups) and main's grouped catalogue (drawn vines). -/
theorem normalChartSupply_of_tvine (hT : TVine.Chart.TVineChartStatement) (γ : ℝ) : NormalChartSupply γ := by
  intro V D _ _ _ M hM S a b hN
  obtain ⟨hV, hnb⟩ := hN
  have hnI : ¬ M.IsVine .I S a b := fun h => hnb (Or.inl h)
  have hnII : ¬ M.IsVine .II S a b := fun h => hnb (Or.inr h)
  rcases hV with ⟨hγ, hE⟩ | ⟨hγ, X, hX⟩
  · have hT' : M.IsTVine S a b := by
      rcases hE with h | h | h
      · exact absurd h hnI
      · exact absurd h hnII
      · exact h
    obtain ⟨F, hF⟩ := hT V D M hM S a b hT'
    refine ⟨F, hF.trans ?_⟩
    unfold famGroups
    simp only [hnI, hnII, hγ, dite_false, ite_true]
  · have h : ∃ X : VineType, M.IsVine X S a b := ⟨X, hX⟩
    have hne1 : h.choose ≠ .I := fun he => hnI (he ▸ h.choose_spec)
    have hne2 : h.choose ≠ .II := fun he => hnII (he ▸ h.choose_spec)
    obtain ⟨F, hF⟩ := exists_normal_chart_of_drawn hM h.choose_spec (isBad_false_of_ne hne1 hne2)
      (VineEstS2.chosenRealization h.choose_spec)
    refine ⟨F, hF.trans ?_⟩
    have hγ' : ¬ γ ≤ 1 / 2 := not_le.mpr hγ
    unfold famGroups
    simp only [hnI, hnII, hγ', h, dite_false, ite_false, dite_true]

end WaveTurbulence.GammaLow.Famb
