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

/-- `hT` with the representative's actual data and layering, without an alignment assumption. -/
theorem sourceClass_hT {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden w)
    (T : Finset (LayeredGarden w)) (hT : (T : Set (LayeredGarden w)) = a.outputs (p := p) (kind := kind)) :
    (T : Set (LayeredGarden w)) = (sourceStart a).allCoreOutputs (p := p) (kind := kind) :=
  classSum_hT a T hT (sourceLayer a) (sourceLayer_isLayering a) (sourceLayer_reconstructs a)

/-- Every genuine unit-class member maps into the literal exported profile garden. -/
noncomputable def sourceShape {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    SpliceShape (fun j => unitClBlock (y.2 j)) a.fullProfile.piece.gap.garden :=
  classShape (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy

theorem source_disj {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden w)
    (y : UState w (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    Disj (fun j => unitClBlock (y.2 j)) :=
  class_disj (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy

/-- R-HINGE with the producer's literal profile hinge set. -/
theorem sourceShape_hinges {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    (sourceShape a y hy).hinges (source_disj a y hy) = a.fullProfile.piece.hinges :=
  classShape_hinges (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy rfl

/-- R-IDX on the exact class member and source-unit carriers. -/
theorem source_upper_tree_index {w p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden w)
    (y : UState w (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma).length) :
    (y.2 j).blk.a.1.1 = (sourceUnits a j).blk.a.1.1 :=
  class_upper_tree_index (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy j

/-- The complete prescribed-point `hmom` field is common across the class. -/
theorem sourceShape_hmom {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    (sourceShape a y hy).hmom (source_disj a y hy) =
      (profileShape a).hmom (unitBlk_disj (Mole.garden_isMolecule _) a.totalSigma) :=
  classShape_hmom (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy

/-- The complete prescribed-point `hclk` field is common across the class. -/
theorem sourceShape_hclk {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind) :
    (sourceShape a y hy).hclk (source_disj a y hy) =
      (profileShape a).hclk (unitBlk_disj (Mole.garden_isMolecule _) a.totalSigma) :=
  classShape_hclk (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy

/-- The actual prescribed-point route is common across the class. -/
theorem sourceShape_route {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain) :
    (sourceShape a y hy).route y.1.plain hG = (profileShape a).route a.prime.prime.1 hG :=
  classShape_route (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy hG

/-- R-SLOT on the literal common profile garden, for all native type profiles. -/
theorem sourceShape_slotFn {R p d : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R))
    (y : UState (2 * R) (unitsSplit (sourceAssembly a))) (hy : y ∈ sourceClass a p kind)
    (hG : a.fullProfile.piece.gap.garden.IsPlain)
    (f : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (L γ δ : ℝ)
    (s : ReplacementSlot a.fullProfile.piece.gap.garden) :
    slotFn y.1.data y.1.plain L γ δ (typeProfiles y.1.layered f) (stateLayer y.1) (stateLayer_isLayering y.1)
      ((sourceShape a y hy).iota y.1.plain hG s) =
    slotFn a.prime.data a.prime.prime.1 L γ δ (typeProfiles a.layered f)
      (sourceLayer a) (sourceLayer_isLayering a) ((profileShape a).iota a.prime.prime.1 hG s) := by
  have h := classShape_slotFn (Mole.garden_isMolecule _) a.totalSigma a.prime.data a.prime.prime.1
    (sourceLayer a) (sourceLayer_isLayering a) a.prime.prime y hy hG f L γ δ s
  rw [sourceLayer_reconstructs] at h
  exact h

end WaveTurbulence.VineAlign
