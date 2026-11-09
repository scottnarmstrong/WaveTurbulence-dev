/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Vine.A.VineMarkedClasses` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedPartition
public import WaveTurbulence.Foundations.Vine.A.VineMarkedClasses
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Amend7
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Deg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Final
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Greg
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Piece
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleDesig
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.TripleHinge
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvEquiv
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvGood
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvIso
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvMap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineCoarseGardenPartition
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFamilyUnique
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineBatch
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineFamily
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineOperation
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRebase
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRecovery
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineFineRefinement
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineGroupExtension
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkFn
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineMarkTransport
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineUnitCover
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescription
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrimeState
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineReindex
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineSelectedTransport
/-! B1b-2: the coarse′ and fine′ classes of a marking function `mk` (SCOPE B0-STAGE1MK §3, §5 R11–R12).

* `Stage1Mk.MarkInvariantBatchV γ mk Clean` is the corrected Lemma 2⁺(a), batch form (ruling R166), with the body of the
  world's `Flower.MkMark.MarkInvariantBatchV` verbatim: every LF batch at unmarked vines of `𝒱` out of a `Clean`
  reconstruction carries the marking.  The world proves it for `markI0` with `Clean := True` and for `markI` with
  `StemCleanV`; main only consumes it.
* Coarse′ classes (`VineA.coarseStateMk`, twists at the unmarked vines of `𝒱`) are rebased at any member
  (`coarse_outputs_rebaseMk`) and are disjoint or equal (`coarse_outputs_disjoint_or_eqMk`), given the coarse
  transport `MarkInvariantBatchV γ mk fun _ => True`.  The proof runs the fine machinery at the all-`SG` prescription,
  whose unmarked `𝒱₀` is exactly `𝒱 ∖ Mk` (`VineA.vinesV0_allSG`).
* Fine′ classes (`VineA.BatchReach`/`VineA.Related` at `mk`) keep their output set (`VineA.Related.outputs_eqMk`) when every fine batch
  carries the marking (`VineA.FineTransportedAt`, from `MarkInvariantBatchV γ mk Clean` at clean points). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Fama.Stage1Mk
open WaveTurbulence.Stage1Mk WaveTurbulence.GammaLow.FinalCount
open WaveTurbulence.Stage1 WaveTurbulence.VineA WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- **Corrected Lemma 2⁺(a), batch form** (ruling R166; body of the world's `Flower.MkMark.MarkInvariantBatchV`,
verbatim): every family member is an unmarked vine of `𝒱`. -/
def MarkInvariantBatchV (γ : ℝ) [Fact (γ ≤ 1 / 2)] (mk : MarkFn γ w) (Clean : ∀ {LG : LayeredGarden w}, VineA.PrimeData LG → Prop) : Prop :=
  ∀ {p : ℕ} {kind : Bool} {ι : Type} {L : List ι} {A B : LFTwist.FamilyReconstruction w ι}
    (h : LFTwist.FamilyBatch p kind L A B) (hA : Reg.Skeleton.IsPrimeGarden A.skeleton),
    (∀ i, ∃ c ∈ vinesVG γ A.skeleton, c.atoms = A.family.atoms i ∧
      c ∉ mk (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered)) →
    Clean (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered) →
    MarkTransported γ (VineA.batchMolIso h)
      (mk (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered))
      (mk (⟨B.skeleton, VineA.batch_prime h hA, B.data, B.decodes⟩ : VineA.PrimeData B.layered))

/-- The empty marking is invariant along every batch (main's Stage 1). -/
theorem markInvariantBatchV_empty (Clean : ∀ {LG : LayeredGarden w}, VineA.PrimeData LG → Prop) :
    MarkInvariantBatchV γ (fun _ => ∅) Clean :=
  fun h _ _ _ => markTransported_empty (VineA.batchMolIso h)

end WaveTurbulence.GammaLow.Fama.Stage1Mk

namespace WaveTurbulence.GammaLow.Fama.VineA
open WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton WaveTurbulence.GammaLow.FinalCount

variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- At the all-`SG` prescription the unmarked `𝒱₀` is the unmarked carrier `𝒱 ∖ Mk` of the coarse′ state. -/
theorem vinesV0_allSG (G : Garden w) (Mk : Set (CLVineG γ G)) :
    vinesV0 γ G (fun _ => .SG) Mk = {c | c ∈ vinesVG γ G ∧ c ∉ Mk} := by
  ext c
  constructor
  · rintro ⟨hc, _, _, _, _, hcM⟩
    exact ⟨hc, hcM⟩
  · rintro ⟨hc, hcM⟩
    have hc' := hc
    obtain ⟨S, hS, hi, _⟩ := hc'
    exact ⟨hc, S, hS, hi, rfl, hcM⟩

/-- The coarse′ state γ is an exact selected family at the all-`SG` prescription. -/
theorem coarseStateMk_isV0Fam (A : PrimeData LG) (Mk : Set (CLVineG γ A.skeleton)) :
    IsV0Fam γ (coarseStateMk γ A Mk).family (fun _ => .SG) Mk := by
  constructor
  · intro i
    have he : familyVine γ (coarseStateMk γ A Mk).family i = i.1 := clVine_eq_of_atoms rfl
    rw [he]
    exact (Set.ext_iff.mp (vinesV0_allSG A.skeleton Mk) i.1).mpr i.2.1
  · intro c hc hcore
    exact ⟨⟨c, (Set.ext_iff.mp (vinesV0_allSG A.skeleton Mk) c).mp hc, hcore⟩, rfl⟩

/-- The coarse′ outputs are the fine′ outputs at the all-`SG` prescription. -/
theorem coarseStateMk_outputs_allSG (A : PrimeData LG) (Mk : Set (CLVineG γ A.skeleton)) :
    (coarseStateMk γ A Mk).allCoreOutputs (p := p) (kind := kind) =
      (PrimeData.fineState γ A (fun _ => .SG) Mk).allCoreOutputs (p := p) (kind := kind) :=
  PrimeData.state_allCoreOutputs_congr A (vinesV0_allSG A.skeleton Mk).symm _ _

/-- B1b-2 (Mk-general form of `VineA.PrimeData.coarse_outputs_rebase`): coarse′ output sets can be rebased at any member's
prime representative, when the coarse marking is carried by every batch (`MarkInvariantBatchV γ mk fun _ => True`; the
world's `markInvariantBatchV_markI0`). -/
theorem PrimeData.coarse_outputs_rebaseMk {mk : Stage1Mk.MarkFn γ w}
    (hV : Stage1Mk.MarkInvariantBatchV γ mk fun _ => True) (A : PrimeData LG) (B : PrimeData LH)
    (h : LH ∈ (coarseStateMk γ A (mk A)).allCoreOutputs (p := p) (kind := kind)) :
    (coarseStateMk γ A (mk A)).allCoreOutputs (p := p) (kind := kind) =
      (coarseStateMk γ B (mk B)).allCoreOutputs (p := p) (kind := kind) := by
  obtain ⟨C, ⟨L, hL, hbatch⟩, he⟩ := (congruent_layered_iff p kind (coarseStateMk γ A (mk A)) LH).mp h
  have hT := hV hbatch A.prime (fun i => ⟨i.1, i.2.1.1, rfl, i.2.1.2⟩) trivial
  have hr := fine_outputs_rebaseMk hbatch hL A.prime (fun _ => .SG) (coarseStateMk_isV0Fam A (mk A)) hT
  subst he
  have hr' : (coarseStateMk γ A (mk A)).allCoreOutputs (p := p) (kind := kind) =
      (PrimeData.fineState γ (⟨C.skeleton, batch_prime hbatch A.prime, C.data, C.decodes⟩ : PrimeData C.layered)
        (fun _ => .SG) (mk (⟨C.skeleton, batch_prime hbatch A.prime, C.data, C.decodes⟩ : PrimeData C.layered))).allCoreOutputs
        (p := p) (kind := kind) := hr
  rw [← coarseStateMk_outputs_allSG] at hr'
  have hu : (⟨C.skeleton, batch_prime hbatch A.prime, C.data, C.decodes⟩ : PrimeData C.layered) = B :=
    primeData_unique _ _
  rw [hu] at hr'
  exact hr'

/-- B1b-2 (Mk-general form of `VineA.PrimeData.coarse_outputs_disjoint_or_eq`). -/
theorem PrimeData.coarse_outputs_disjoint_or_eqMk {mk : Stage1Mk.MarkFn γ w}
    (hV : Stage1Mk.MarkInvariantBatchV γ mk fun _ => True) (A : PrimeData LG) (B : PrimeData LH) :
    Disjoint ((coarseStateMk γ A (mk A)).allCoreOutputs (p := p) (kind := kind))
      ((coarseStateMk γ B (mk B)).allCoreOutputs (p := p) (kind := kind)) ∨
    (coarseStateMk γ A (mk A)).allCoreOutputs (p := p) (kind := kind) =
      (coarseStateMk γ B (mk B)).allCoreOutputs (p := p) (kind := kind) := by
  classical
  by_cases hd : Disjoint ((coarseStateMk γ A (mk A)).allCoreOutputs (p := p) (kind := kind))
      ((coarseStateMk γ B (mk B)).allCoreOutputs (p := p) (kind := kind))
  · exact Or.inl hd
  · right
    obtain ⟨K, hKA, hKB⟩ := Set.not_disjoint_iff.mp hd
    have hpK : K.garden.IsPlain := by
      obtain ⟨C, _, he⟩ := (congruent_layered_iff p kind (coarseStateMk γ A (mk A)) K).mp hKA
      rw [← he]
      exact C.decodes.1
    let E := primeDataOf K hpK
    exact (PrimeData.coarse_outputs_rebaseMk hV A E hKA).trans (PrimeData.coarse_outputs_rebaseMk hV B E hKB).symm

namespace PrescribedPrimeGarden

/-- B1b-2: every fine′ batch out of `a` carries the fine marking `mk`. -/
def FineTransportedAt (γ : ℝ) [Fact (γ ≤ 1 / 2)] (mk : Stage1Mk.MarkFn γ w) (a : PrescribedPrimeGarden γ w) : Prop :=
  ∀ {p : ℕ} {kind : Bool} {L : List (CoreIndex γ (vinesV0 γ a.prime.skeleton a.totalSigma (mk a.prime)))}
    {B : FamilyReconstruction w (CoreIndex γ (vinesV0 γ a.prime.skeleton a.totalSigma (mk a.prime)))}
    (h : FamilyBatch p kind L (a.state γ mk) B),
    Stage1Mk.MarkTransported γ (batchMolIso h) (mk a.prime)
      (mk (⟨B.skeleton, batch_prime h a.prime.prime, B.data, B.decodes⟩ : PrimeData B.layered))

/-- The empty marking is carried by every fine batch. -/
theorem fineTransportedAt_empty (a : PrescribedPrimeGarden γ w) : a.FineTransportedAt γ (fun _ => ∅) :=
  fun h => Stage1Mk.markTransported_empty (batchMolIso h)






/-- B1b-2: a fine′ batch edge stays inside the coarse′ class of its source (for a coarse marking below the fine one),
with no transport hypothesis on the fine marking. -/
theorem BatchReach.mem_coarseMk {mkF mkC : Stage1Mk.MarkFn γ w}
    (hsub : ∀ {LG : LayeredGarden w} (A : PrimeData LG), mkC A ⊆ mkF A) {a b : PrescribedPrimeGarden γ w}
    (h : BatchReach γ (p := p) (kind := kind) a b mkF) :
    b.layered ∈ (coarseStateMk γ a.prime (mkC a.prime)).allCoreOutputs (p := p) (kind := kind) := by
  obtain ⟨L, B, hb, hL, rfl⟩ := h
  exact PrimeData.fine_outputs_subset_coarseMk a.prime a.totalSigma (hsub a.prime)
    ((congruent_layered_iff p kind (a.state γ mkF) B.layered).mpr ⟨B, ⟨L, hL, hb⟩, rfl⟩)

/-- Transport of a group prescription along the identity. -/
theorem transportGroupPrescription_refl {G : Garden w} (σ : Represents.GroupPrescription γ G) :
    transportGroupPrescription γ (molIsoRefl G) σ = σ := by
  funext T
  refine congrArg σ (Subtype.ext ?_)
  change T.1.image (Equiv.refl _) = T.1
  rw [Equiv.coe_refl, Finset.image_id]

/-- B1b-2: with no runs/units at the marking there is no unmarked selected core vine. -/
theorem isEmpty_coreIndex_of_unitBlocks_nil {G : Garden w} {σ : Prescription G} {Mk : Set (CLVineG γ G)}
    (hnv : unitBlocks γ G σ Mk = []) : IsEmpty (CoreIndex γ (vinesV0 γ G σ Mk)) :=
  ⟨fun c => by
    obtain ⟨_, _, u, hu, -⟩ := (vinesV0_iff_unit_coverMk G σ c.1).mp c.2.1
    rw [hnv] at hu
    exact absurd hu List.not_mem_nil⟩

/-- B1b-2: with no runs/units at the marking, `𝒱₀♮` is empty. -/
theorem not_mem_vinesV0_of_unitBlocks_nil {G : Garden w} {σ : Prescription G} {Mk : Set (CLVineG γ G)}
    (hnv : unitBlocks γ G σ Mk = []) (c : CLVineG γ G) : c ∉ vinesV0 γ G σ Mk := fun hc => by
  obtain ⟨_, _, u, hu, -⟩ := (vinesV0_iff_unit_coverMk G σ c).mp hc
  rw [hnv] at hu
  exact absurd hu List.not_mem_nil

/-- A batch over an empty index type is trivial: the prescribed point is unchanged. -/
theorem ofState_eq_of_isEmpty {mk : Stage1Mk.MarkFn γ w} (a : PrescribedPrimeGarden γ w)
    [IsEmpty (CoreIndex γ (vinesV0 γ a.prime.skeleton a.totalSigma (mk a.prime)))]
    {L : List (CoreIndex γ (vinesV0 γ a.prime.skeleton a.totalSigma (mk a.prime)))}
    {B : FamilyReconstruction w (CoreIndex γ (vinesV0 γ a.prime.skeleton a.totalSigma (mk a.prime)))}
    (hb : FamilyBatch p kind L (a.state γ mk) B) (hL : L.Perm Finset.univ.toList) :
    ofState γ B (batch_prime hb a.prime.prime) (transportGroupPrescription γ (batchMolIso hb) a.sigma) = a := by
  have h0 : (Finset.univ : Finset (CoreIndex γ (vinesV0 γ a.prime.skeleton a.totalSigma (mk a.prime)))).toList = [] := by
    simp [Finset.univ_eq_empty]
  rw [h0] at hL
  obtain rfl : L = [] := List.Perm.eq_nil hL
  have hs := batchMolIso_spec hb
  generalize batchMolIso hb = F at hs ⊢
  generalize batch_prime hb a.prime.prime = hpB
  cases hs
  exact (congrArg (ofState γ (a.state γ mk) hpB) (transportGroupPrescription_refl a.sigma)).trans rfl

/-- B1b-2: a fine′ batch edge out of a point without units at the marking is trivial. -/
theorem batchReach_eq_of_unitBlocks_nil {mk : Stage1Mk.MarkFn γ w} {a b : PrescribedPrimeGarden γ w}
    (hnv : unitBlocks γ a.prime.skeleton a.totalSigma (mk a.prime) = [])
    (h : BatchReach γ (p := p) (kind := kind) a b mk) : b = a := by
  haveI := isEmpty_coreIndex_of_unitBlocks_nil hnv
  obtain ⟨L, B, hb, hL, rfl⟩ := h
  exact ofState_eq_of_isEmpty a hb hL

/-- B1b-2: a fine′ batch edge *into* a point without units at the marking is trivial (the source's unmarked family is
carried onto the target's, which is empty). -/
theorem batchReach_eq_of_unitBlocks_nil' {mk : Stage1Mk.MarkFn γ w} {a b : PrescribedPrimeGarden γ w}
    (hT : a.FineTransportedAt γ mk) (hnv : unitBlocks γ b.prime.skeleton b.totalSigma (mk b.prime) = [])
    (h : BatchReach γ (p := p) (kind := kind) a b mk) : a = b := by
  obtain ⟨L, B, hb, hL, rfl⟩ := h
  have hB := BatchIso.selectedMk (batchMolIso_spec hb) a.totalSigma _ _ (fineState_isV0FamMk a.prime a.totalSigma) (hT hb)
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      extendGroupPrescription γ (transportGroupPrescription γ (batchMolIso hb) a.sigma) :=
    transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [ht] at hB
  haveI : IsEmpty (CoreIndex γ (vinesV0 γ a.prime.skeleton a.totalSigma (mk a.prime))) :=
    ⟨fun i => not_mem_vinesV0_of_unitBlocks_nil hnv _ (hB.1 i)⟩
  exact (ofState_eq_of_isEmpty a hb hL).symm

/-- B1b-2: along a fine′ relation, being the unit-free point `a` is invariant. -/
theorem related_eq_iff_of_unitBlocks_nil {mk : Stage1Mk.MarkFn γ w}
    (hT : ∀ c : PrescribedPrimeGarden γ w, c.FineTransportedAt γ mk) {a : PrescribedPrimeGarden γ w}
    (hnv : unitBlocks γ a.prime.skeleton a.totalSigma (mk a.prime) = []) {x y : PrescribedPrimeGarden γ w}
    (hxy : Related γ (p := p) (kind := kind) x y mk) : x = a ↔ y = a := by
  induction hxy with
  | rel x' y' hr =>
    constructor
    · rintro rfl; exact batchReach_eq_of_unitBlocks_nil hnv hr
    · rintro rfl; exact batchReach_eq_of_unitBlocks_nil' (hT x') hnv hr
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

/-- B1b-2: the fine′ class of a point without units at the marking is the point itself. -/
theorem related_eq_of_unitBlocks_nil {mk : Stage1Mk.MarkFn γ w} (hT : ∀ c : PrescribedPrimeGarden γ w, c.FineTransportedAt γ mk)
    {a b : PrescribedPrimeGarden γ w} (hnv : unitBlocks γ a.prime.skeleton a.totalSigma (mk a.prime) = [])
    (h : Related γ (p := p) (kind := kind) a b mk) : b = a :=
  (related_eq_iff_of_unitBlocks_nil hT hnv h).mp rfl

end PrescribedPrimeGarden
end WaveTurbulence.GammaLow.Fama.VineA
