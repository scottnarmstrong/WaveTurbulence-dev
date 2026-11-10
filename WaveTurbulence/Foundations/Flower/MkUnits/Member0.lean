/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.Code
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD2
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD3
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD5
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD6

/-! # MK-UNITS: the member geometry of a run class at a marking

Main's `RepVD1`, `RepVD2`, `RepVD5`–`RepVD7` (layers of a member through its shape, slot boxes, the common selection
`selSkC`, the trace data of a member's shape) at the marking `mk`, on the spliced garden
`(stSt a.prime.skeleton a.totalSigma (mk a.prime)).G` of the representative.  A member `y` gets the shape `memShape`: B1b-3's
`commonShapeMk` of its chosen full trace, with the image marking along that trace (no member marking hypothesis).


Adapted from main's `RepVD1.lean`, `RepVD2.lean`, `RepVD5.lean`, `RepVD6.lean`, `RepVD7.lean` (see
`COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice WaveTurbulence.VineB
  WaveTurbulence.LGSpine WaveTurbulence.VineEstS2 WaveTurbulence.Stage1 WaveTurbulence.Vine WaveTurbulence.VineA
  WaveTurbulence.VineEstS4 WaveTurbulence.VineC WaveTurbulence.LFTwist WaveTurbulence.VineAlign
  WaveTurbulence.RegRedLeaf WaveTurbulence.Represents WaveTurbulence.VineA.PrescribedPrimeGarden

variable {w p : ℕ} {kind : Bool}

theorem member_core_layerMk (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w)
    (y : UState w (unitsSplit (sourceAssemblyMk a mk))) (M : List (UnitsIndex (sourceAssemblyMk a mk)))
    (hr : ReachU p kind (unitsSplit (sourceAssemblyMk a mk)).Q M (sourceStart a mk) (sourceUnitsMk a mk) y.1 y.2)
    (b : GBranch a.prime.skeleton.tree) :
    stateLayer y.1 (y.1.data.coreBranch y.1.plain ((batchMolIso hr.batch).e b)).toNode =
      sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode := by
  have h := BatchIso.coreLayer (batchMolIso_spec hr.batch) b
  rw [coreLayer_of_spec y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) y.1.layered
    (stateLayer_spec y.1)] at h
  rw [h]
  exact coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    (sourceStart a mk).layered rfl _ b

section Shape
variable {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)

include hy

/-- **The shape of a run-class member**: B1b-3's common shape of the chosen full trace, the marking carried by its
image (`markTransported_imageMark`).  Unlike `sourceShapeMk`, it needs no member marking along every trace. -/
noncomputable def memShape :
    SpliceShape (fun j => unitClBlock (y.2 j)) (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G :=
  commonShapeMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a)
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.2
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.1
    (markTransported_imageMark _ (mk a.prime))

/-- The member's shape is the common shape of a full trace (main's `sourceShape_data` at a marking). -/
theorem memShape_data :
    ∃ (M : List (UnitsIndex (sourceAssemblyMk a mk)))
      (hr : ReachU p kind (unitsSplit (sourceAssemblyMk a mk)).Q M (sourceStart a mk) (sourceUnitsMk a mk) y.1 y.2)
      (hn : M.Nodup), memShape a mk y hy =
        commonShapeMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
          (sourceLayer a) (sourceLayer_isLayering a) hr hn (markTransported_imageMark _ (mk a.prime)) := by
  obtain ⟨hn, hr⟩ := (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec
  exact ⟨_, hr, hn, rfl⟩

/-- R-HINGE for the member's shape. -/
theorem memShape_hinges :
    (memShape a mk y hy).hinges (source_disjMk a mk y hy) = (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges :=
  commonShape_hingesMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.2
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.1 (markTransported_imageMark _ (mk a.prime))

theorem memShape_hmom :
    (memShape a mk y hy).hmom (source_disjMk a mk y hy) =
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hmom
        (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) :=
  commonShape_hmomMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.2
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.1 (markTransported_imageMark _ (mk a.prime))

theorem memShape_hclk :
    (memShape a mk y hy).hclk (source_disjMk a mk y hy) =
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).hclk
        (unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) :=
  commonShape_hclkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.2
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.1 (markTransported_imageMark _ (mk a.prime))

theorem memShape_route (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain) :
    (memShape a mk y hy).route y.1.plain hG =
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG :=
  commonShape_routeMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.2
    (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
      (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec.1 (markTransported_imageMark _ (mk a.prime)) hG

/-- The trace data of a member's shape (main's `sourceShape_trace` at a marking). -/
theorem memShape_trace :
    ∃ (M : List (UnitsIndex (sourceAssemblyMk a mk)))
      (hr : ReachU p kind (unitsSplit (sourceAssemblyMk a mk)).Q M (sourceStart a mk) (sourceUnitsMk a mk) y.1 y.2),
      (∀ c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree,
        (memShape a mk y hy).br c =
          (batchMolIso hr.batch).e ((stSt a.prime.skeleton a.totalSigma (mk a.prime)).M.ob c)) ∧
      ∀ j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length,
        (y.2 j).blk.b = (batchMolIso hr.batch).e
          (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).lower := by
  obtain ⟨hn, hr⟩ := (class_member_traceMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy).choose_spec
  refine ⟨_, hr, fun c => commonShape_brMk _ _ _ _ _ _ hr hn _ c, fun j => ?_⟩
  exact (reachU_coordinates hr hn (batchMolIso_spec hr.batch) j).2.2

/-- Core layers through a member's shape are the piece layers of the representative. -/
theorem memShape_core_layer (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    stateLayer y.1 (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode =
      (a.normalizedPiece 0 (mk a.prime)).layer c := by
  obtain ⟨M, hr, hbr, -⟩ := memShape_trace a mk y hy
  rw [hbr c, member_core_layerMk a mk y M hr]
  exact (coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
    (sourceLayer_reconstructs a) a.prime.decodes _).symm

/-- Main's `member_lay_eq` at a marking. -/
theorem memShape_lay_eq :
    (fun c => stateLayer y.1 (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode) =
      (a.normalizedPiece 0 (mk a.prime)).layer :=
  funext (memShape_core_layer a mk y hy)

omit hy in
/-- Core layers through the representative's shape. -/
theorem shape_core_layerMk (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) :
    sourceLayer a (a.prime.data.coreBranch a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).toNode =
      (a.normalizedPiece 0 (mk a.prime)).layer c :=
  (coreLayer_of_spec a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
    (sourceLayer_reconstructs a) a.prime.decodes _).symm

/-- The clock layers of the outer slots are common to the class (main's `sourceShape_clkLayer` at a marking). -/
theorem memShape_clkLayer (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (s : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (i : Fin 2) :
    clkLayer p (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode)
        (argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s) i) =
      clkLayer p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode)
        (argSrc a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s)
          i) := by
  obtain ⟨M, hr, hbr, hlow⟩ := memShape_trace a mk y hy
  have hroute := congrFun (congrFun (memShape_route a mk y hy hG) s) i
  rcases hr' : (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route
      a.prime.prime.1 hG s i with y' | j
  · rw [hr'] at hroute
    rw [(memShape a mk y hy).route_inl _ hG hroute,
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route_inl _ hG hr']
    rcases y' with r | c
    · rfl
    · show stateLayer y.1 (y.1.data.coreBranch y.1.plain ((memShape a mk y hy).br c)).toNode =
        sourceLayer a (a.prime.data.coreBranch a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c)).toNode
      rw [memShape_core_layer, shape_core_layerMk]
  · rw [hr'] at hroute
    rw [(memShape a mk y hy).route_inr _ hG hroute,
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route_inr _ hG hr']
    show stateLayer y.1 (y.1.data.coreBranch y.1.plain (y.2 j).blk.b).toNode =
      sourceLayer a (a.prime.data.coreBranch a.prime.prime.1
        (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).lower).toNode
    rw [hlow j]
    exact member_core_layerMk a mk y M hr _

/-- Main's `sourceShape_slotBox` at a marking. -/
theorem memShape_slotBox (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (s : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    slotBox p (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode) y.1.plain
        ((memShape a mk y hy).iota y.1.plain hG s) =
      slotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s) := by
  rcases s with q | c
  · have h0 := memShape_clkLayer a mk y hy hG (Sum.inl q) 0
    have h1 := memShape_clkLayer a mk y hy hG (Sum.inl q) 1
    simp only [SpliceShape.iota] at h0 h1 ⊢
    simp only [slotBox, h0, h1]
  · have h0 := memShape_clkLayer a mk y hy hG (Sum.inr c) 0
    have h1 := memShape_clkLayer a mk y hy hG (Sum.inr c) 1
    simp only [SpliceShape.iota] at h0 h1 ⊢
    simp only [slotBox, h0, h1]

end Shape

/-! ## The common selection at a marking -/

section Sel
variable {R : ℕ}

/-- The fine′ class gap functional at the marking is B1b-3's `gapValueMk` of the representative. -/
theorem profileMk_gap_value (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) {d : ℕ}
    (L γ η : ℝ) (hL : L ≠ 0) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G d roots 0) :
    (a.profileMk mk).gap.value d L γ η hL base roots z =
      NormalizedSplice.gapValueMk a.prime.skeleton a.totalSigma (mk a.prime) L γ η base z.1 := rfl

/-- The common selection of `G_sb` at the marking: the gap functional of the fine′ class is `1`. -/
def selSkCMk (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) {d : ℕ} (L γ η : ℝ) (_hL : L ≠ 0)
    (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G d roots 0) : Prop :=
  NormalizedSplice.gapValueMk a.prime.skeleton a.totalSigma (mk a.prime) L γ η base z.1 = 1

open scoped Classical in
theorem gapValueMk_01 (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) {d : ℕ} (L γ η : ℝ)
    (base : Mom d) (z : GNode (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree → (Fin d → ℤ)) :
    NormalizedSplice.gapValueMk a.prime.skeleton a.totalSigma (mk a.prime) L γ η base z = 0 ∨
      NormalizedSplice.gapValueMk a.prime.skeleton a.totalSigma (mk a.prime) L γ η base z = 1 := by
  let D' : SplicedKernelData (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G d :=
    ⟨fun _ => 0, ∅, fun _ => 0, fun _ _ => 0, fun _ => 0,
      NormalizedSplice.gapSpecificationMk a.prime.skeleton a.totalSigma (mk a.prime), fun _ => 0, fun _ => 0⟩
  rw [NormalizedSplice.gapValue_eq_indicatorMk a.totalSigma D' rfl L γ η base z]
  exact splicedGapIndicator_01 _ D' L γ η base z

open scoped Classical in
theorem gapValueMk_ite (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) {d : ℕ} (L γ η : ℝ)
    (hL : L ≠ 0) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G d roots 0) :
    NormalizedSplice.gapValueMk a.prime.skeleton a.totalSigma (mk a.prime) L γ η base z.1 =
      if selSkCMk a mk L γ η hL base roots z then 1 else 0 := by
  rcases gapValueMk_01 a mk L γ η base z.1 with h | h
  · rw [if_neg (by unfold selSkCMk; rw [h]; norm_num), h]
  · rw [if_pos (by unfold selSkCMk; exact h), h]

open scoped Classical in
theorem selSkCMk_ite (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) {d : ℕ} (L γ η : ℝ)
    (hL : L ≠ 0) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G d roots 0) :
    (a.profileMk mk).gap.value d L γ η hL base roots z = if selSkCMk a mk L γ η hL base roots z then 1 else 0 := by
  rw [profileMk_gap_value]
  exact gapValueMk_ite a mk L γ η hL base roots z

open scoped Classical in
/-- The literal gap indicator of the marked piece is the common selection (the `hgsp` hypothesis of main's
`representsIntA_of_vineModes`). -/
theorem normalizedPiece_gapIndicatorMk (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) {d : ℕ}
    (D : SplicedKernelData (a.normalizedPiece d (mk a.prime)).Gsb d)
    (hD : D.gapSpecification = (a.normalizedPiece d (mk a.prime)).gapSpecification)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ))
    (z : GenDecoration (a.normalizedPiece d (mk a.prime)).Gsb d roots 0) :
    splicedGapIndicator (a.normalizedPiece d (mk a.prime)).Gsb D L γ η base z.1 =
      if selSkCMk a mk L γ η hL base roots z then 1 else 0 := by
  rw [← gapValueMk_ite a mk L γ η hL base roots z]
  exact (NormalizedSplice.gapValue_eq_indicatorMk a.totalSigma D hD L γ η base z.1).symm

end Sel

end WaveTurbulence.Flower.MkUnits
