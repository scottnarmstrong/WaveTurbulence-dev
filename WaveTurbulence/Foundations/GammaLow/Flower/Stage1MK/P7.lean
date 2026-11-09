/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.Vine.A.VineFineRefinement
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.Vine.A.VinePieceProfile
public import WaveTurbulence.Foundations.Vine.A.VinePlainA4
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VineNormalizationNamesSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Supp.VinePrescribedPointsSupp
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupExtension
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedPiece
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt

/-! # FLOWER-LOW (packet L8), item I (wave 7): item-I declarations of modules ported only in part by L5a

Main's `VineA.PrescribedPrimeGarden.{outputs, mem_outputs_selfMk, Related.outputs_eqMk, tauClass_imageMk, profileMk}`,
`VineA.coarseAtomWord_twist`, `VineA.familyPieceProfileMk` (in modules L5a ported only for its own cone), copied by source
(sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.VineA
open Stage1 Twist RedSplice LFTwist Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- B1b (R11): every prescribed garden belongs to its fine′ output class. -/
theorem mem_fine_outputs_selfMkLow (A : PrimeData LG) (σ : Prescription A.skeleton)
    (Mk : Set (Fama.CLVineG γF A.skeleton)) :
    LG ∈ (Fama.VineA.PrimeData.fineState γF A σ Mk).allCoreOutputs (p := p) (kind := kind) :=
  (congruent_layered_iff p kind (Fama.VineA.PrimeData.fineState γF A σ Mk) LG).mpr
    ⟨Fama.VineA.PrimeData.fineState γF A σ Mk, WaveTurbulence.Stage1.Congruent.refl p kind (Fama.VineA.PrimeData.fineState γF A σ Mk), rfl⟩

alias _root_.WaveTurbulence.VineA.PrimeData.mem_fine_outputs_selfMkLow := mem_fine_outputs_selfMkLow

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist Reg.Skeleton Represents
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w p : ℕ} {kind : Bool}

/-- The actual once-per-member garden output set. -/
def _root_.WaveTurbulence.GammaLow.Fama.VineA.PrescribedPrimeGarden.outputsLow (a : Fama.VineA.PrescribedPrimeGarden γF w) (mk : Fama.Stage1Mk.MarkFn γF w := fun _ => ∅) : Set (LayeredGarden w) :=
  (a.state γF mk).allCoreOutputs (p := p) (kind := kind)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- B1b-2 (Mk-general form of `Fama.VineA.PrescribedPrimeGarden.BatchReach.outputs_eq`): a fine′ batch edge keeps the fine′ output set. -/
theorem _root_.WaveTurbulence.GammaLow.Fama.VineA.PrescribedPrimeGarden.BatchReach.outputs_eqMkLow {mk : Fama.Stage1Mk.MarkFn γF w} {a b : Fama.VineA.PrescribedPrimeGarden γF w}
    (hT : a.FineTransportedAt γF mk) (h : Fama.VineA.PrescribedPrimeGarden.BatchReach γF (p := p) (kind := kind) a b mk) :
    a.outputsLow (p := p) (kind := kind) mk = b.outputsLow (p := p) (kind := kind) mk := by
  obtain ⟨L, B, hb, hL, rfl⟩ := h
  have hr := Fama.VineA.fine_outputs_rebaseMk hb hL a.prime.prime a.totalSigma
    (Fama.VineA.fineState_isV0FamMk a.prime a.totalSigma) (hT hb)
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      Fama.VineA.extendGroupPrescription γF (Fama.VineA.transportGroupPrescription γF (batchMolIso hb) a.sigma) :=
    Fama.VineA.transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [ht] at hr
  exact hr

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- B1b-2 (Mk-general form of `Fama.VineA.PrescribedPrimeGarden.Related.outputs_eq`). -/
theorem _root_.WaveTurbulence.GammaLow.Fama.VineA.PrescribedPrimeGarden.Related.outputs_eqMkLow {mk : Fama.Stage1Mk.MarkFn γF w} (hT : ∀ c : Fama.VineA.PrescribedPrimeGarden γF w, c.FineTransportedAt γF mk)
    {a b : Fama.VineA.PrescribedPrimeGarden γF w} (h : Fama.VineA.PrescribedPrimeGarden.Related γF (p := p) (kind := kind) a b mk) :
    a.outputsLow (p := p) (kind := kind) mk = b.outputsLow (p := p) (kind := kind) mk := by
  induction h with
  | rel _ _ h => exact Fama.VineA.PrescribedPrimeGarden.BatchReach.outputs_eqMkLow (hT _) h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- B1b-2 (Mk-general form of `Fama.VineA.PrescribedPrimeGarden.mem_outputs_self`). -/
theorem _root_.WaveTurbulence.GammaLow.Fama.VineA.PrescribedPrimeGarden.mem_outputs_selfMkLow (mk : Fama.Stage1Mk.MarkFn γF w) (a : Fama.VineA.PrescribedPrimeGarden γF w) :
    a.layered ∈ a.outputsLow (p := p) (kind := kind) mk := a.prime.mem_fine_outputs_selfMkLow a.totalSigma (mk a.prime)

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Stage1 WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- B1b-2 (Mk-general form of `Fama.VineA.PrescribedPrimeGarden.tauClass_image`): exact garden projection of a fine′ class. -/
theorem _root_.WaveTurbulence.GammaLow.Fama.VineA.PrescribedPrimeGarden.tauClass_imageMkLow {mk : Fama.Stage1Mk.MarkFn γF w} (hT : ∀ c : Fama.VineA.PrescribedPrimeGarden γF w, c.FineTransportedAt γF mk)
    (a : Fama.VineA.PrescribedPrimeGarden γF w) :
    Fama.VineA.PrescribedPrimeGarden.layered '' a.tauClassLow (p := p) (kind := kind) mk = a.outputsLow (p := p) (kind := kind) mk := by
  ext LG
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Fama.VineA.PrescribedPrimeGarden.Related.outputs_eqMkLow hT hb]
    exact Fama.VineA.PrescribedPrimeGarden.mem_outputs_selfMkLow mk b
  · intro hLG
    obtain ⟨B, ⟨L, hL, hb⟩, he⟩ := (congruent_layered_iff p kind (a.state γF mk) LG).mp hLG
    let b := Fama.VineA.PrescribedPrimeGarden.ofState γF B (batch_prime hb a.prime.prime) (Fama.VineA.transportGroupPrescription γF (batchMolIso hb) a.sigma)
    exact ⟨b, Relation.EqvGen.rel a b ⟨L, B, hb, hL, rfl⟩, he⟩

end

section
open WaveTurbulence.VineA
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open Stage1 RedSplice LFTwist LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w R p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}

/-- B1b-3 (Mk-general form of `familyPieceProfile`): the piece fields at the marking `Mk`. -/
noncomputable def familyPieceProfileMkLow (A : FamilyReconstruction (2 * R) ι) (σ : Prescription A.skeleton)
    (Mk : Set (Fama.CLVineG γF A.skeleton)) : PieceProfile (2 * R) where
  gap := vineA_gapProfileMkLow A.skeleton σ Mk
  layer := (Fama.VineA.NormalizedSplice.stage1PieceOf γF 0 A.plain A.layered A.decodes σ Mk).layer
  hinges := (Fama.VineA.NormalizedSplice.stage1PieceOf γF 0 A.plain A.layered A.decodes σ Mk).Cs.hinges
  gsk := (Fama.VineA.NormalizedSplice.stage1PieceOf γF 0 A.plain A.layered A.decodes σ Mk).gsk
  bsk := (Fama.VineA.NormalizedSplice.stage1PieceOf γF 0 A.plain A.layered A.decodes σ Mk).bsk

end

section
open WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open Stage1 RedSplice LFTwist LGSpine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {R p : ℕ} {kind : Bool}

/-- B1b-3 (Mk-general form of `profile`): the piece profile (gap functional, layers, hinges, counts) of the fine′
Fama.VineA.PrescribedPrimeGarden.state γF at the marking `mk`. -/
noncomputable def _root_.WaveTurbulence.GammaLow.Fama.VineA.PrescribedPrimeGarden.profileMkLow (a : Fama.VineA.PrescribedPrimeGarden γF (2 * R)) (mk : Fama.Stage1Mk.MarkFn γF (2 * R)) : PieceProfile (2 * R) :=
  familyPieceProfileMkLow (a.state γF mk) a.totalSigma (mk a.prime)

end

end WaveTurbulence.GammaLow.Flower
