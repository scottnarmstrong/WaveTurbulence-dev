/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.Stage1.Geometry.SurvConnMK

/-! # B2c MK-SUBPRO (world side), part 1: the survivors `𝒞_E` of the marked splice as world `SurvivorData`

`survData G σ Mk prot` lists the survivors of `stSt G σ Mk` chain by chain (main's `survObjs`, B2c), with the
protected set `prot` (`Π_sb`, supplied by B4).  On it:
* `survData_structural`: `SurvivorData.Structural` (ruling R169: first conjunct `ObjVine`) for
  `collectionChoices G σ Mk` — o75 Theorem 7.5′(2) (`𝒞_E` vines/HVs disjoint from `𝒞₁`, consecutive survivors share at
  most one joint) and the hinge clause;
* `survData_chainOrder`: `SurvChainOrder` (finding F-C0-5, o75 §4.6 chain order).
-/

@[expose] public section
set_option autoImplicit false

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset
open WaveTurbulence.RedSplice (Prescription stSt survivorsMk)

namespace WaveTurbulence.Flower.MkSubpro
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

variable {w : ℕ}

/-- **The survivors of the marked splice** as world `SurvivorData` (`m` = their number, `surv` = main's `survObjs`,
`prot` = the protected set from B4). -/
noncomputable def survData (G : Garden w) (σ : Prescription G) (Mk : Set (Stage1.CLVine G))
    (prot : Finset (GBranch (stSt G σ Mk).G.tree)) : SurvivorData (stSt G σ Mk).G :=
  ⟨(VineA.NormalizedSplice.survObjs G σ Mk).length, (VineA.NormalizedSplice.survObjs G σ Mk).get, prot⟩

/-- **`SurvivorData.Structural`** (R169) for the survivors of the marked splice and `𝒞₁ = collectionChoices G σ Mk`. -/
theorem survData_structural (G : Garden w) (σ : Prescription G) (Mk : Set (Stage1.CLVine G))
    (prot : Finset (GBranch (stSt G σ Mk).G.tree)) :
    (survData G σ Mk prot).Structural (VineA.NormalizedSplice.collectionChoices G σ Mk) := by
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  refine ⟨fun i => ?_, fun i j => ?_, fun i j hij => ?_, fun v hv i => ?_⟩
  · obtain ⟨j, hj, -, hgi⟩ := VineA.NormalizedSplice.survObjs_get (σ := σ) (Mk := Mk) i
    change FinalCountAsm.ObjVine _ ((VineA.NormalizedSplice.survObjs G σ Mk).get i)
    rw [hgi]
    exact VineA.NormalizedSplice.survObj_objVine hj
  · obtain ⟨j', hj', -, hgj⟩ := VineA.NormalizedSplice.survObjs_get (σ := σ) (Mk := Mk) j
    change Disjoint ((VineA.NormalizedSplice.objects G σ Mk).get i).atoms
      ((VineA.NormalizedSplice.survObjs G σ Mk).get j).atoms
    rw [hgj]
    exact VineA.NormalizedSplice.objects_disjoint_survObj hM σ (List.get_mem _ _) hj'
  · exact VineA.NormalizedSplice.survObjs_inter_card hM σ i j hij
  · obtain ⟨j, hj, -, hgi⟩ := VineA.NormalizedSplice.survObjs_get (σ := σ) (Mk := Mk) i
    change ¬ ((VineA.NormalizedSplice.survObjs G σ Mk).get i).IsInterior v
    rw [hgi]
    exact VineA.NormalizedSplice.survObj_not_interior hj hv

/-- **`SurvChainOrder`** (F-C0-5) for the survivors of the marked splice: survivors meet only index-consecutive
survivors (they are listed chain by chain, in spine order). -/
theorem survData_chainOrder (G : Garden w) (σ : Prescription G) (Mk : Set (Stage1.CLVine G))
    (prot : Finset (GBranch (stSt G σ Mk).G.tree)) : SurvChainOrder (survData G σ Mk prot) :=
  fun i j hij hm =>
    VineA.NormalizedSplice.survObjs_chainOrder (WaveTurbulence.Mole.garden_isMolecule G) σ i j hij hm

end WaveTurbulence.Flower.MkSubpro
