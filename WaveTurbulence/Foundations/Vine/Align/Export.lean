/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.ClassBoundary
public import WaveTurbulence.Foundations.Vine.Align.ClassKernels
/-! S2 geometry and class-set export. The actual common-garden shape, route,
boundary, unit index, hinges and output-set bridge are supplied here.
Native outer-slot kernels also agree as complete functions of times and momentum. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 VineA VineB VineC RedSplice Stage1 Twist RegRed Represents LFTwist Reg.Skeleton LGSpine

/-- Pull the representative's actual layering to its decoded reconstruction. -/
noncomputable def sourceLayer {w : ℕ} (a : PrescribedPrimeGarden w) :
    GNode (a.prime.data.forest a.prime.prime.1) → ℕ :=
  (layered_eq_reconstruction a.prime.data a.prime.prime.1 a.layered a.prime.decodes).choose

theorem sourceLayer_isLayering {w : ℕ} (a : PrescribedPrimeGarden w) :
    IsLayering (a.prime.data.garden a.prime.prime.1) (sourceLayer a) :=
  (layered_eq_reconstruction a.prime.data a.prime.prime.1 a.layered a.prime.decodes).choose_spec.choose

theorem sourceLayer_reconstructs {w : ℕ} (a : PrescribedPrimeGarden w) :
    layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) = a.layered :=
  (layered_eq_reconstruction a.prime.data a.prime.prime.1 a.layered a.prime.decodes).choose_spec.choose_spec

/-- B1a: the actual unit assembly family for the marking `mk` (the units are the runs of the marked groups, so the
start family consists of unmarked vines only); main's `sourceAssembly a` is its value at the empty marking. -/
noncomputable abbrev sourceAssemblyMk {w : ℕ} (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w) :=
  alignedAssemblyMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)

/-- B1a: the unit regions for the marking `mk`. -/
noncomputable abbrev sourceUnitsMk {w : ℕ} (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w) :=
  unitsRegion (sourceAssemblyMk a mk) (VineB.unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime))

/-- The actual unit assembly family to use as `B₀` in the S2 class sum. -/
noncomputable abbrev sourceAssembly {w : ℕ} (a : PrescribedPrimeGarden w) :=
  sourceAssemblyMk a fun _ => ∅

noncomputable abbrev sourceStart {w : ℕ} (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w := fun _ => ∅) :=
  unitsStart (sourceAssemblyMk a mk) (VineB.unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime))
    a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)

noncomputable abbrev sourceUnits {w : ℕ} (a : PrescribedPrimeGarden w) :=
  sourceUnitsMk a fun _ => ∅

noncomputable abbrev sourceClass {w : ℕ} (a : PrescribedPrimeGarden w) (p : ℕ) (kind : Bool)
    (mk : Stage1Mk.MarkFn w := fun _ => ∅) :=
  classU (unitsSplit (sourceAssemblyMk a mk)) p kind (sourceStart a mk) (sourceUnitsMk a mk)

section SourceMk
/-! B1b-3: the exported class-shape lemmas at a marking `mk`. A member `y` of `sourceClass a p kind mk` carries the
marking `mkY` (`SourceMemberMarked`); the shapes land on the representative's spliced garden at `mk a.prime`. -/
variable {w p : ℕ} {kind : Bool}

/-- B1b-3: the member `y` of the marked source class carries `mkY` along every actual trace. -/
abbrev SourceMemberMarked (a : PrescribedPrimeGarden w) (p : ℕ) (kind : Bool) (mk : Stage1Mk.MarkFn w)
    (y : UState w (unitsSplit (sourceAssemblyMk a mk))) (mkY : Set (CLVine y.1.skeleton)) : Prop :=
  MemberMarked p kind (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) y mkY

/-- B1b-3: the empty marking is carried to every member of the unmarked source class. -/
theorem sourceMemberMarked_empty (a : PrescribedPrimeGarden w) (p : ℕ) (kind : Bool)
    (y : UState w (unitsSplit (sourceAssemblyMk a fun _ => ∅))) : SourceMemberMarked a p kind (fun _ => ∅) y ∅ :=
  memberMarked_empty p kind _ _ _ _ _ _ y

/-- B1b-3 (Mk-general form of `sourceClass_hT`). -/
theorem sourceClass_hTMk (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w)
    (T : Finset (LayeredGarden w)) (hT : (T : Set (LayeredGarden w)) = a.outputs (p := p) (kind := kind) mk) :
    (T : Set (LayeredGarden w)) = (sourceStart a mk).allCoreOutputs (p := p) (kind := kind) :=
  classSum_hTMk a mk T hT (sourceLayer a) (sourceLayer_isLayering a) (sourceLayer_reconstructs a)

variable (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w)
  (y : UState w (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)

include hy

/-- B1b-3 (Mk-general form of `sourceShape`): every member maps into the spliced garden at the marking. -/
noncomputable def sourceShapeMk {mkY : Set (CLVine y.1.skeleton)} (hT : SourceMemberMarked a p kind mk y mkY) :
    SpliceShape (fun j => unitClBlock (y.2 j)) (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G :=
  classShapeMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy hT

/-- B1b-3 (Mk-general form of `source_disj`). -/
theorem source_disjMk : Disj (fun j => unitClBlock (y.2 j)) :=
  class_disjMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy

/-- B1b-3 (Mk-general form of `sourceShape_hinges`): R-HINGE at the marking. -/
theorem sourceShape_hingesMk {mkY : Set (CLVine y.1.skeleton)} (hT : SourceMemberMarked a p kind mk y mkY) :
    (sourceShapeMk a mk y hy hT).hinges (source_disjMk a mk y hy) =
      (stSt a.prime.skeleton a.totalSigma (mk a.prime)).hinges :=
  classShape_hingesMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy hT

/-- B1b-3 (Mk-general form of `source_upper_tree_index`). -/
theorem source_upper_tree_indexMk (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    (y.2 j).blk.a.1.1 = (sourceUnitsMk a mk j).blk.a.1.1 :=
  class_upper_tree_indexMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy j

/-- B1b-3 (Mk-general form of `sourceShape_hmom`). -/
theorem sourceShape_hmomMk {mkY : Set (CLVine y.1.skeleton)} (hT : SourceMemberMarked a p kind mk y mkY) :
    (sourceShapeMk a mk y hy hT).hmom (source_disjMk a mk y hy) =
      (stShape (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)).hmom
        (unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)) :=
  classShape_hmomMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy hT

/-- B1b-3 (Mk-general form of `sourceShape_hclk`). -/
theorem sourceShape_hclkMk {mkY : Set (CLVine y.1.skeleton)} (hT : SourceMemberMarked a p kind mk y mkY) :
    (sourceShapeMk a mk y hy hT).hclk (source_disjMk a mk y hy) =
      (stShape (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)).hclk
        (unitBlkMk_disj (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)) :=
  classShape_hclkMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy hT

/-- B1b-3 (Mk-general form of `sourceShape_route`). -/
theorem sourceShape_routeMk {mkY : Set (CLVine y.1.skeleton)} (hT : SourceMemberMarked a p kind mk y mkY)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain) :
    (sourceShapeMk a mk y hy hT).route y.1.plain hG =
      (stShape (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)).route a.prime.prime.1 hG :=
  classShape_routeMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy hT hG

/-- B1b-3 (Mk-general form of `sourceShape_slotFn`): R-SLOT at the marking. -/
theorem sourceShape_slotFnMk {d : ℕ} {mkY : Set (CLVine y.1.skeleton)} (hT : SourceMemberMarked a p kind mk y mkY)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ)
    (s : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    slotFn y.1.data y.1.plain L γ δ (typeProfiles y.1.layered f) (stateLayer y.1) (stateLayer_isLayering y.1)
      ((sourceShapeMk a mk y hy hT).iota y.1.plain hG s) =
    slotFn a.prime.data a.prime.prime.1 L γ δ (typeProfiles a.layered f)
      (sourceLayer a) (sourceLayer_isLayering a)
      ((stShape (Mole.garden_isMolecule _) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s) := by
  have h := classShape_slotFnMk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy hT hG f L γ δ s
  rw [sourceLayer_reconstructs] at h
  exact h

end SourceMk

/-- `hT` with the representative's actual data and layering, without an alignment assumption. -/
theorem sourceClass_hT {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden w)
    (T : Finset (LayeredGarden w)) (hT : (T : Set (LayeredGarden w)) = a.outputs (p := p) (kind := kind)) :
    (T : Set (LayeredGarden w)) = (sourceStart a).allCoreOutputs (p := p) (kind := kind) :=
  sourceClass_hTMk a (fun _ => ∅) T hT

/-- Every genuine unit-class member maps into the literal exported profile garden. -/
noncomputable def sourceShape {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    SpliceShape (fun j => unitClBlock (y.2 j)) a.fullProfile.piece.gap.garden :=
  classShape (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy

theorem source_disj {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden w)
    (y : UState w (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    Disj (fun j => unitClBlock (y.2 j)) :=
  source_disjMk a (fun _ => ∅) y hy

/-- R-HINGE with the producer's literal profile hinge set. -/
theorem sourceShape_hinges {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    (sourceShape a y hy).hinges (source_disj a y hy) = a.fullProfile.piece.hinges :=
  sourceShape_hingesMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y)

/-- R-IDX on the exact class member and source-unit carriers. -/
theorem source_upper_tree_index {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden w)
    (y : UState w (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length) :
    (y.2 j).blk.a.1.1 = (sourceUnits a j).blk.a.1.1 :=
  source_upper_tree_indexMk a (fun _ => ∅) y hy j

/-- The complete prescribed-point `hmom` field is common across the class. -/
theorem sourceShape_hmom {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    (sourceShape a y hy).hmom (source_disj a y hy) =
      (profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule _) a.totalSigma) :=
  sourceShape_hmomMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y)

/-- The complete prescribed-point `hclk` field is common across the class. -/
theorem sourceShape_hclk {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    (sourceShape a y hy).hclk (source_disj a y hy) =
      (profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule _) a.totalSigma) :=
  sourceShape_hclkMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y)

/-- The actual prescribed-point route is common across the class. -/
theorem sourceShape_route {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain) :
    (sourceShape a y hy).route y.1.plain hG = (profileShape a).route a.prime.prime.1 hG :=
  sourceShape_routeMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y) hG

/-- R-SLOT on the literal common profile garden, for all native type profiles. -/
theorem sourceShape_slotFn {R p d : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (f : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (L γ δ : ℝ)
    (s : ReplacementSlot a.fullProfile.piece.gap.garden) :
    slotFn y.1.data y.1.plain L γ δ (typeProfiles y.1.layered f) (stateLayer y.1) (stateLayer_isLayering y.1)
      ((sourceShape a y hy).iota y.1.plain hG s) =
    slotFn a.prime.data a.prime.prime.1 L γ δ (typeProfiles a.layered f)
      (sourceLayer a) (sourceLayer_isLayering a) ((profileShape a).iota a.prime.prime.1 hG s) :=
  sourceShape_slotFnMk a (fun _ => ∅) y hy (sourceMemberMarked_empty a p kind y) hG f L γ δ s

end WaveTurbulence.VineAlign
