/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK3
public import WaveTurbulence.Foundations.FinalCount.GL21
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO (ruling R171): the gap entry of a marked group

`gapSpecificationMk_marked`: for a marked group `S` of `𝒞`, the gap specification of `G_sb` has an entry at
`π j₀` (`j₀` the upper joint of the first survivor `t₀` of `S`), of kind `σ S`, whose darts are the lifts of the chosen
pair of `t₀` at `j₀` (o75 (2.3): the indicator `𝒵` has a factor for every group of `𝒞`).

The survivor's pair lifts because its darts are not internal to a class of the splice state: for an SG group by B2a's
`survivor_imageMK` (the interior atoms of a survivor are unclassified and `π` is injective on it), for a group of
another kind because nothing in it is spliced.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- An ingredient of a group lies in the group. -/
theorem isIngredient_subset {S T : Finset (GBranch G.tree)} (h : IsIngredient G.molecule S T) : T ⊆ S := by
  rcases h with ⟨_, _, _, _, _, _, hCI⟩ | ⟨_, _, _, _, _, _, _, _, _, hCI⟩
  · exact (Vine.chainIngredient_spec hCI).2.2
  · exact (Vine.chainIngredient_spec hCI).2.2

/-- The first survivor of a marked group. -/
theorem groupSurvMk_head {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)} (hmk : markedGroup G Mk S) :
    ∃ t, (groupSurvMk G Mk S).head? = some t ∧ t ∈ (markedUnitsOfMK hmk).surv := by
  have hg : groupSurvMk G Mk S = (markedUnitsOfMK hmk).surv :=
    groupSurvMk_of_marked hmk (exists_markedGroupUnits hmk)
  obtain ⟨c, hcMk, hcV, hcI⟩ := hmk
  obtain ⟨t, ht, -⟩ := (markedUnitsOfMK ⟨c, hcMk, hcV, hcI⟩).surv_cover c hcMk hcV hcI
  rw [hg]
  cases hs : (markedUnitsOfMK ⟨c, hcMk, hcV, hcI⟩).surv with
  | nil => rw [hs] at ht; cases ht
  | cons t0 l => exact ⟨t0, rfl, List.mem_cons_self⟩

/-- No atom of a group of a kind other than SG is classified by the splice state. -/
theorem cls_none_of_not_SG (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (hσ : σ S ≠ Molecule.GapKind.SG)
    {z : GBranch G.tree} (hz : z ∈ S) : (stSt G σ Mk).cls z = none := by
  apply stSt_cls_noneMk hM σ Mk
  intro u hu hzu
  obtain ⟨S', hS', hσ', hmem⟩ := (mem_unitBlocksMk (Mk := Mk)).mp hu
  have hsub := groupUnitsMk_sub hmem hzu
  by_cases hSS : S = S'
  · exact hσ (hSS ▸ hσ')
  · exact Finset.disjoint_left.mp (groups_disjoint hM hS hS' hSS) hz hsub

/-- **The darts of a survivor are not internal to a class**: a dart inside a survivor `t` of a marked group, at a joint
of `t`, lifts to `G_sb`. -/
theorem survDart_not_internal (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (hmk : markedGroup G Mk S)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ (markedUnitsOfMK hmk).surv)
    {d : GardenDart G} (hd : G.molecule.InGroup t.1 d) (hdj : G.molecule.atom d = t.2.1 ∨ G.molecule.atom d = t.2.2) :
    ¬ ∃ a, (stSt G σ Mk).cls (G.molecule.atom d) = some a ∧
      (stSt G σ Mk).cls (G.molecule.atom (G.molecule.mate d)) = some a := by
  rintro ⟨a, ha1, ha2⟩
  obtain ⟨hvine, hI, -⟩ := (markedUnitsOfMK hmk).surv_spec t ht
  have htS : t.1 ⊆ S := isIngredient_subset hI
  by_cases hσ : σ S = Molecule.GapKind.SG
  · obtain ⟨X, hX⟩ := hvine
    have hloop := FinalCountG3.isVine_noLoop hX d hd.1
    obtain ⟨O, hOat, hOu, hOl, hinj, -, hint, -⟩ := survivor_imageMK hS hσ hmk ht
    have hm : G.molecule.atom (G.molecule.mate d) ∈ t.1 := hd.2
    by_cases hmi : G.molecule.atom (G.molecule.mate d) ≠ t.2.1 ∧ G.molecule.atom (G.molecule.mate d) ≠ t.2.2
    · rw [hint _ hm hmi.1 hmi.2] at ha2; cases ha2
    · -- both ends are joints of `t`: they are distinct atoms in one class, against injectivity of `π`
      have hpi : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (G.molecule.atom d) =
          (stSt G σ Mk).M.pi (stSt G σ Mk).hcls (G.molecule.atom (G.molecule.mate d)) := by
        apply (stSt G σ Mk).M.ob_inj
        rw [(stSt G σ Mk).M.ob_pi, (stSt G σ Mk).M.ob_pi]
        unfold repC
        rw [ha1, ha2]
        rfl
      exact hloop (hinj hd.1 hm hpi)
  · rw [cls_none_of_not_SG hM σ hS hσ (htS hd.1)] at ha1
    cases ha1

end WaveTurbulence.VineA.NormalizedSplice
