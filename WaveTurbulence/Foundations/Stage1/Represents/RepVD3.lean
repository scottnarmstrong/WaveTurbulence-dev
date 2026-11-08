/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVD2
public import WaveTurbulence.Foundations.Stage1.Represents.RepNU7
import Mathlib.Tactic

/-!
# S2 REPRESENTS, session 12: per-member facts (F-Z)

`sourceShape_hZ`: for a class member `y`, the selection of its (transported) group prescription at a skeleton decoration `κ` is the
representative's common gap value `a.fullProfile.piece.gap.value` at the restriction `Φ_y.resDec κ`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign

variable {w p : ℕ} {kind : Bool}

theorem gapProfile_value_cast {Q P : GapProfile w} (hQP : Q = P) (d : ℕ) (L γ η : ℝ) (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration Q.garden d roots 0) :
    Q.value d L γ η hL base roots z =
      P.value d L γ η hL base roots (gardenGenCast (congrArg GapProfile.garden hQP) z) := by
  subst hQP
  rfl

theorem castShape_resDec {S G H : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S}
    (h : G = H) (Φ : SpliceShape blk G) (hS : S.IsPlain) (hd : Disj blk) {d : ℕ} {roots : Fin w → (Fin d → ℤ)}
    (κ : GenDecoration S d roots 0) :
    (castShape h Φ).resDec hS hd κ = gardenGenCast h (Φ.resDec hS hd κ) := by
  subst h
  rfl

theorem reindexShape_resDec {S G : Garden w} {J K : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    {blk : J → CLBlock S} (Φ : SpliceShape blk G) (e : K ≃ J) (hS : S.IsPlain) (hd : Disj blk) {d : ℕ}
    {roots : Fin w → (Fin d → ℤ)} (κ : GenDecoration S d roots 0) :
    (reindexShape Φ e).resDec hS (reindex_disj hd e) κ = Φ.resDec hS hd κ := rfl

theorem congrBlocks_resDec {S G : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk blk' : J → CLBlock S}
    (h : blk = blk') (Φ : SpliceShape blk G) (hS : S.IsPlain) (hd : Disj blk) (hd' : Disj blk') {d : ℕ}
    {roots : Fin w → (Fin d → ℤ)} (κ : GenDecoration S d roots 0) :
    (congrBlocks h Φ).resDec hS hd' κ = Φ.resDec hS hd κ := by
  subst h
  rfl


/-- B1b-3 (Mk-general form of `commonShape_resDec`). -/
theorem commonShape_resDecMk {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S)
    {Mk : Set (CLVine S)} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer)
    {Y : FamilyReconstruction w (UnitsIndex (alignedAssemblyMk hM σ Mk))}
    {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssemblyMk hM σ Mk)).Q j)}
    {L : List (UnitsIndex (alignedAssemblyMk hM σ Mk))}
    (hr : ReachU p kind (unitsSplit (alignedAssemblyMk hM σ Mk)).Q L
      (unitsStart (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk) D hS layer hLayer)
      (unitsRegion (alignedAssemblyMk hM σ Mk) (unitBlkMk_disj hM σ Mk)) Y vs)
    (hn : L.Nodup) {Mk' : Set (CLVine Y.skeleton)} (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) Mk Mk')
    {d : ℕ} {roots : Fin w → (Fin d → ℤ)} (κ : GenDecoration Y.skeleton d roots 0) :
    (commonShapeMk hM σ D hS layer hLayer hr hn hT).resDec Y.plain (member_disjMk hM σ D hS layer hLayer hr hn) κ =
      gardenGenCast ((batchMolIso_spec hr.batch).splice_garden_eqMk σ hT (unitsFamily_isV0FamMk hM σ))
        ((stShape (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ) Mk').resDec
          Y.plain (unitBlkMk_disj (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ)
            Mk') κ) := by
  unfold commonShapeMk endpointShapeMk
  refine (castShape_resDec _ _ _ _ κ).trans (congrArg _ ?_)
  exact (congrBlocks_resDec _ _ _ _ _ κ).trans (reindexShape_resDec _ _ _ _ κ)

open scoped Classical in
/-- B1b-3 (Mk-general form of `hZ_stStN`): from B2c's exact gap identity at `(S, σ, Mk)`
(`SplicedGapIndicatorSelOfAt`, the statement of `splicedGapIndicator_eq_selOfMk`). -/
theorem hZ_stStNMk {S : Garden w} (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S)
    {Mk : Set (CLVine S)} (hgap : VineA.NormalizedSplice.SplicedGapIndicatorSelOfAt S σ Mk) {d : ℕ} {L : ℝ}
    (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (κ : GenDecoration S d roots 0)
    (D : SplicedKernelData (stSt S σ Mk).G d)
    (hD : D.gapSpecification = VineA.NormalizedSplice.gapSpecificationMk S σ Mk) :
    splicedGapIndicator (stSt S σ Mk).G D L γ η base
        ((stShape hM σ Mk).resDec hS (unitBlkMk_disj hM σ Mk) κ).1 =
      if VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base κ.1
        then 1 else 0 :=
  hgap L γ η base _ κ.1 (spliced_molecule_decoration S hS hL base roots κ)
    (fun v _ hv => gardenSource_eq_zero_of_deg_four S hS _ v hv) _ (fun y => bondIndex_stSt_odMk hM σ κ.1 y) D hD

open scoped Classical in
/-- B1b-3 (Mk-general form of `gapValue_stShape`). -/
theorem gapValue_stShapeMk {S : Garden w} (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S)
    {Mk : Set (CLVine S)} (hgap : VineA.NormalizedSplice.SplicedGapIndicatorSelOfAt S σ Mk) {d : ℕ}
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (κ : GenDecoration S d roots 0) :
    NormalizedSplice.gapValueMk S σ Mk L γ η base
        ((stShape hM σ Mk).resDec hS (unitBlkMk_disj hM σ Mk) κ).1 =
      if NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base κ.1 then 1 else 0 := by
  let D' : SplicedKernelData (stSt S σ Mk).G d :=
    ⟨fun _ => 0, ∅, fun _ => 0, fun _ _ => 0, fun _ => 0, NormalizedSplice.gapSpecificationMk S σ Mk, fun _ => 0,
      fun _ => 0⟩
  rw [NormalizedSplice.gapValue_eq_indicatorMk σ D' rfl]
  exact hZ_stStNMk hM hS σ hgap hL γ η base roots κ D' rfl

theorem commonShape_resDec {S : Garden w} (hM : S.molecule.IsMolecule) (σ : Prescription S)
    (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer)
    {Y : FamilyReconstruction w (UnitsIndex (alignedAssembly hM σ))}
    {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (alignedAssembly hM σ)).Q j)}
    {L : List (UnitsIndex (alignedAssembly hM σ))}
    (hr : ReachU p kind (unitsSplit (alignedAssembly hM σ)).Q L
      (unitsStart (alignedAssembly hM σ) (unitBlk_disj hM σ) D hS layer hLayer)
      (unitsRegion (alignedAssembly hM σ) (unitBlk_disj hM σ)) Y vs)
    (hn : L.Nodup) {d : ℕ} {roots : Fin w → (Fin d → ℤ)} (κ : GenDecoration Y.skeleton d roots 0) :
    (commonShape hM σ D hS layer hLayer hr hn).resDec Y.plain (member_disj hM σ D hS layer hLayer hr hn) κ =
      gardenGenCast ((batchMolIso_spec hr.batch).splice_garden_eq σ (unitsFamily_isV0Fam hM σ))
        ((stShape (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ)).resDec
          Y.plain (unitBlk_disj (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) σ)) κ) :=
  commonShape_resDecMk hM σ D hS layer hLayer hr hn (Stage1Mk.markTransported_empty _) κ


open scoped Classical in
/-- `NormalizedSplice.gapValue` at the restriction of a skeleton decoration is `[selOf σ]` (no kernel data needed). -/
theorem gapValue_stShape {S : Garden w} (hM : S.molecule.IsMolecule) (hS : S.IsPlain) (σ : Prescription S) {d : ℕ}
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (κ : GenDecoration S d roots 0) :
    NormalizedSplice.gapValue S σ L γ η base
        ((stShape hM σ).resDec hS (unitBlk_disj hM σ) κ).1 =
      if NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base κ.1 then 1 else 0 :=
  gapValue_stShapeMk hM hS σ (NormalizedSplice.splicedGapIndicatorSelOfAt_empty S σ) hL γ η base roots κ

theorem ofPrescription_transport_total (a : PrescribedPrimeGarden w) {H : Garden w}
    (F : MolIso a.prime.skeleton.molecule H.molecule) :
    NormalizedSplice.GroupPrescription.ofPrescription (transportPrescription F a.totalSigma) =
      transportGroupPrescription F a.sigma := by
  rw [PrescribedPrimeGarden.totalSigma, transport_extendGroupPrescription]
  exact of_extendGroupPrescription _

open scoped Classical in
/-- B1b-3 (Mk-general form of `hZ_common`): for a member `Y` of the marked source class carrying the marking `Mk'`,
the selection at a decoration `κ` of `Y` is the representative's gap value at the marking (`a.profileMk mk`) at the
restriction `Φ_Y.resDec κ`. Hypothesis: B2c's dart-label gap identity at every garden (`GapValueSelDartsMk`); its
z-form at the member (`SplicedGapIndicatorSelOfAt`) follows by `splicedGapIndicatorSelOfAt_of_selDarts`. -/
theorem hZ_commonMk {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
    {Y : FamilyReconstruction (2 * R) (UnitsIndex (sourceAssemblyMk a mk))}
    {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (sourceAssemblyMk a mk)).Q j)}
    {L : List (UnitsIndex (sourceAssemblyMk a mk))}
    (hr : ReachU p kind (unitsSplit (sourceAssemblyMk a mk)).Q L (sourceStart a mk) (sourceUnitsMk a mk) Y vs)
    (hn : L.Nodup) {Mk' : Set (CLVine Y.skeleton)}
    (hT : Stage1Mk.MarkTransported (batchMolIso hr.batch) (mk a.prime) Mk') (hg : GapValueSelDartsMk (2 * R))
    {d : ℕ} {Lc : ℝ} (hL : Lc ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (κ : GenDecoration Y.skeleton d roots 0) :
    (if NormalizedSplice.selOf (transportGroupPrescription (batchMolIso hr.batch) a.sigma) Lc γ η base κ.1
      then (1 : ℝ) else 0) =
    (a.profileMk mk).gap.value d Lc γ η hL base roots
      ((commonShapeMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
        (sourceLayer a) (sourceLayer_isLayering a) hr hn hT).resDec Y.plain
        (member_disjMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
          (sourceLayer a) (sourceLayer_isLayering a) hr hn) κ) := by
  rw [commonShape_resDecMk]
  have hQP := (batchMolIso_spec hr.batch).gapProfileMk a.totalSigma hT
    (unitsFamily_isV0FamMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma) hg
  have h1 := gapValue_stShapeMk (Mole.garden_isMolecule Y.skeleton) Y.plain
    (transportPrescription (batchMolIso hr.batch) a.totalSigma) (Mk := Mk')
    (NormalizedSplice.splicedGapIndicatorSelOfAt_of_selDarts (hg _ _ Mk')) hL γ η base roots κ
  have h2 := gapProfile_value_cast hQP d Lc γ η hL base roots
    ((stShape (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) a.totalSigma) Mk').resDec
      Y.plain (unitBlkMk_disj (Mole.garden_isMolecule Y.skeleton)
        (transportPrescription (batchMolIso hr.batch) a.totalSigma) Mk') κ)
  exact (congrArg (fun σ => if NormalizedSplice.selOf σ Lc γ η base κ.1 then (1 : ℝ) else 0)
    (ofPrescription_transport_total a (batchMolIso hr.batch)).symm).trans (h1.symm.trans h2)

open scoped Classical in
theorem hZ_common {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    {Y : FamilyReconstruction (2 * R) (UnitsIndex (sourceAssembly a))}
    {vs : ∀ j, UnitAt Y.skeleton Y.family ((unitsSplit (sourceAssembly a)).Q j)}
    {L : List (UnitsIndex (sourceAssembly a))}
    (hr : ReachU p kind (unitsSplit (sourceAssembly a)).Q L (sourceStart a) (sourceUnits a) Y vs)
    (hn : L.Nodup) {d : ℕ} {Lc : ℝ} (hL : Lc ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (κ : GenDecoration Y.skeleton d roots 0) :
    (if NormalizedSplice.selOf (transportGroupPrescription (batchMolIso hr.batch) a.sigma) Lc γ η base κ.1
      then (1 : ℝ) else 0) =
    a.fullProfile.piece.gap.value d Lc γ η hL base roots
      ((commonShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
        (sourceLayer a) (sourceLayer_isLayering a) hr hn).resDec Y.plain
        (member_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
          (sourceLayer a) (sourceLayer_isLayering a) hr hn) κ) := by
  rw [commonShape_resDec]
  have hQP := (batchMolIso_spec hr.batch).gapProfile a.totalSigma
    (unitsFamily_isV0Fam (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma)
  have h1 := gapValue_stShape (Mole.garden_isMolecule Y.skeleton) Y.plain
    (transportPrescription (batchMolIso hr.batch) a.totalSigma) hL γ η base roots κ
  have h2 := gapProfile_value_cast hQP d Lc γ η hL base roots
    ((stShape (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) a.totalSigma)).resDec
      Y.plain (unitBlk_disj (Mole.garden_isMolecule Y.skeleton) (transportPrescription (batchMolIso hr.batch) a.totalSigma)) κ)
  exact (congrArg (fun σ => if NormalizedSplice.selOf σ Lc γ η base κ.1 then (1 : ℝ) else 0)
    (ofPrescription_transport_total a (batchMolIso hr.batch)).symm).trans (h1.symm.trans h2)

end WaveTurbulence.Represents
