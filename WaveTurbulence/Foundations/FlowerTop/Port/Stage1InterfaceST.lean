/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1Interface
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedKernelST
public import WaveTurbulence.Foundations.FlowerTop.Port.TypeFamilyST
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
/-! AMEND-ST (R61 X4): Stage 1 pieces with STUBS, as a generalization of `Stage1Interface`.

`Stage1PieceDST` extends `Stage1PieceD` by the stub set `stubs` of the spliced garden; `RepresentsIntST` is
`RepresentsInt` with the stub time `ts` (the spliced kernels are `splicedKernelST`, stubs held at `ts`);
`RepresentsST` adds the garden-side identity with the stub kernel (`LeafFamily.valueSelFix`, FlowerP1Stub, adopted
verbatim) and the anchored leaf family; `Stage1PieceDST.Sound` adds `stub_pendant` (`StubPendant`): the stubs lie
in no hinge, selected object, maximal ladder or gap specification. With no stubs everything is the current data
(`Stage1PieceD.toST`, `RepresentsIntST.toOld`, `Sound.toST`, `Sound.toOld`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical

/-- AMEND-ST: data of one Stage 1 piece with stubs: a piece together with its stub branches. -/
structure Stage1PieceDST (d R : ℕ) extends Stage1PieceD d R where
  /-- The stub branches of the spliced garden (pendant: see `StubPendant`). -/
  stubs : Finset (GBranch Gsb.tree)

abbrev Stage1PieceST (P : WTParams) (R : ℕ) := Stage1PieceDST P.d R

/-- A piece without stubs. -/
def Stage1PieceD.toST {d R : ℕ} (π : Stage1PieceD d R) : Stage1PieceDST d R := { π with stubs := ∅ }

/-- The spliced kernel data (with stubs at time `ts`) of a piece. -/
def Stage1PieceDST.data {P : WTParams} {R : ℕ} (π : Stage1PieceST P R) (tt : Fin (2 * R) → ℝ) (ts : ℝ)
    (center : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : GBranch π.Gsb.tree → ℝ) : SplicedKernelDataST π.Gsb P.d where
  toSplicedKernelData := Stage1Piece.data π.toStage1PieceD tt center edge hinge freq
  stubs := π.stubs
  stubTime := ts

/-- Stub pendancy (R61: "stubs are pendant: never in a block, vine, ladder or regular object"), on the spliced
garden: the stubs are not hinges, lie in no selected object (`C.collection`), in no maximal ladder, and carry no
local gap specification. -/
def StubPendant {w : ℕ} (G : Garden w) (C : SourceVine.SubproChoices G)
    (gs : ∀ v : GBranch G.tree, Option (LocalGapSpecification G v)) (stubs : Finset (GBranch G.tree)) : Prop :=
  (∀ b ∈ stubs, b ∉ C.hinges) ∧ (∀ i, ∀ b ∈ stubs, b ∉ (C.collection i).atoms) ∧
    (∀ S ∈ G.molecule.maximalLadders, ∀ b ∈ stubs, b ∉ S) ∧ (∀ b ∈ stubs, gs b = none)

/-- The part of `StubPendant` that does not involve the selected objects (hinges, ladders, gap specifications). -/
def StubPendantLadder {w : ℕ} (G : Garden w) (hinges : Finset (GBranch G.tree))
    (gs : ∀ v : GBranch G.tree, Option (LocalGapSpecification G v)) (stubs : Finset (GBranch G.tree)) : Prop :=
  (∀ b ∈ stubs, b ∉ hinges) ∧ (∀ S ∈ G.molecule.maximalLadders, ∀ b ∈ stubs, b ∉ S) ∧
    (∀ b ∈ stubs, gs b = none)

theorem StubPendant.toLadder {w : ℕ} {G : Garden w} {C : SourceVine.SubproChoices G}
    {gs : ∀ v : GBranch G.tree, Option (LocalGapSpecification G v)} {stubs : Finset (GBranch G.tree)}
    (h : StubPendant G C gs stubs) : StubPendantLadder G C.hinges gs stubs :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem stubPendant_empty {w : ℕ} (G : Garden w) (C : SourceVine.SubproChoices G)
    (gs : ∀ v : GBranch G.tree, Option (LocalGapSpecification G v)) :
    StubPendant G C gs ∅ := by
  simp [StubPendant]

theorem stubPendantLadder_empty {w : ℕ} (G : Garden w) (hinges : Finset (GBranch G.tree))
    (gs : ∀ v : GBranch G.tree, Option (LocalGapSpecification G v)) :
    StubPendantLadder G hinges gs ∅ := by
  simp [StubPendantLadder]

/-- `RepresentsInt` with stubs (R61 X4): the integral conjunct, the stub time `ts` in the spliced kernels. -/
def Stage1PieceDST.RepresentsIntST {P : WTParams} {R : ℕ} (π : Stage1PieceST P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (ts : ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ)
    (val : ℂ) : Prop :=
  ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (μ : Measure Ξ) (w : Ξ → ℂ)
    (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Integrable (fun ξ => w ξ * splicedKernelST π.Gsb (π.data tt ts (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots) μ ∧
    val = ∫ ξ, w ξ * splicedKernelST π.Gsb (π.data tt ts (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∂μ ∧
    Integrable (fun ξ => ‖w ξ‖) μ ∧
    (∫ ξ, ‖w ξ‖ ∂μ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * s) ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (π.data tt ts (ctr ξ) (edge ξ) (hinge ξ) (freq ξ)).toSplicedKernelData

/-- **Bridge**: a stub-free piece represents an integral in the new sense iff in the old sense. -/
theorem Stage1PieceDST.RepresentsIntST.toOld {P : WTParams} {R : ℕ} (π : Stage1PieceST P R)
    (hs : π.stubs = ∅) {n : ℕ} {tt : Fin (2 * R) → ℝ} {ts : ℝ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s : ℝ} {val : ℂ}
    (h : π.RepresentsIntST n tt ts base roots s val) :
    Stage1Piece.RepresentsInt (P := P) π.toStage1PieceD n tt base roots s val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb, hD⟩ := h
  have hk : ∀ ξ, splicedKernelST π.Gsb (π.data tt ts (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots =
      splicedKernel π.Gsb (Stage1Piece.data (P := P) π.toStage1PieceD tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
        P.L P.γ P.η P.δ base roots := fun ξ =>
    (splicedKernel_eq_splicedKernelST (π.data tt ts (ctr ξ) (edge ξ) (hinge ξ) (freq ξ)) hs
      P.L P.γ P.η P.δ base roots).symm
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, ?_, ?_, hwint, hwb, hD⟩
  · simpa only [hk] using hint
  · rw [hv]; simp only [hk]

/-- **Bridge**: a stub-free piece in the old sense represents the same integral in the new sense. -/
theorem Stage1Piece.RepresentsInt.toST {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (ts : ℝ)
    {n : ℕ} {tt : Fin (2 * R) → ℝ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} {s : ℝ} {val : ℂ}
    (h : π.RepresentsInt n tt base roots s val) :
    π.toST.RepresentsIntST n tt ts base roots s val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb, hD⟩ := h
  have hk : ∀ ξ, splicedKernelST π.toST.Gsb (π.toST.data tt ts (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots =
      splicedKernel π.Gsb (Stage1Piece.data (P := P) π (tt) (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
        P.L P.γ P.η P.δ base roots := fun ξ =>
    (splicedKernel_eq_splicedKernelST (π.toST.data tt ts (ctr ξ) (edge ξ) (hinge ξ) (freq ξ)) rfl
      P.L P.γ P.η P.δ base roots).symm
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, ?_, ?_, hwint, hwb, hD⟩
  · simpa only [hk] using hint
  · rw [hv]; simp only [hk]

/-- The garden-side value of an anchored family with stubs: the stub kernels `LeafFamily.valueSelFix`
(FlowerP1Stub) of the family `U.toLFAnch J`, stubs `stubs LG` at the time `ts`. -/
noncomputable def Stage1PieceDST.gardenValue {P : WTParams} {R : ℕ} (U : TypeFamily P (2 * R))
    (J : Finset (Fin (2 * R))) (tt : Fin (2 * R) → ℝ) (ts : ℝ)
    (stubs : ∀ LG : LayeredGarden (2 * R), Finset (GBranch LG.garden.tree)) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop) : ℂ :=
  ∑ LG ∈ members, (U.toLFAnch J).valueSelFix tt (fun LG' => FlowerP1.stubFix (stubs LG') ts) base roots LG (sel LG)

/-- `Represents` with stubs and anchors (R61 X4): the garden-side stub-kernel identity and `RepresentsIntST`. -/
def Stage1PieceDST.RepresentsST {P : WTParams} {R : ℕ} (π : Stage1PieceST P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (ts : ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (U : TypeFamily P (2 * R)) (J : Finset (Fin (2 * R)))
    (stubs : ∀ LG : LayeredGarden (2 * R), Finset (GBranch LG.garden.tree))
    (s : ℝ) (val : ℂ) : Prop :=
  val = Stage1PieceDST.gardenValue U J tt ts stubs base roots members sel ∧ π.RepresentsIntST n tt ts base roots s val

/-- `Stage1Piece.Sound` with the stub-pendant clause (R61 X4; S2a and S4 produce the stub set and prove it). -/
structure Stage1PieceDST.Sound {P : WTParams} {R : ℕ} (π : Stage1PieceST P R) (p : ℕ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) : Prop
    extends Stage1Piece.Sound (P := P) π.toStage1PieceD p base roots where
  stub_pendant : StubPendant π.Gsb π.Cs π.gapSpecification π.stubs

/-- **Bridge**: a sound stub-free piece is sound in the new sense. -/
theorem Stage1Piece.Sound.toST {P : WTParams} {R : ℕ} {π : Stage1Piece P R} {p : ℕ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (h : π.Sound p base roots) : π.toST.Sound p base roots :=
  { toSound := h, stub_pendant := stubPendant_empty _ _ _ }

/-- **Bridge**: `Stage1PieceDST.Sound` implies the old `Sound` of the underlying piece. -/
theorem Stage1PieceDST.Sound.toOld {P : WTParams} {R : ℕ} {π : Stage1PieceST P R} {p : ℕ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (h : π.Sound p base roots) :
    Stage1Piece.Sound (P := P) π.toStage1PieceD p base roots := h.toSound

end WaveTurbulence.LGSpine
