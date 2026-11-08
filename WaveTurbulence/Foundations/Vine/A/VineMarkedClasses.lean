/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedPartition
/-! B1b-2: the coarse′ and fine′ classes of a marking function `mk` (SCOPE B0-STAGE1MK §3, §5 R11–R12).

* `Stage1Mk.MarkInvariantBatchV mk Clean` is the corrected Lemma 2⁺(a), batch form (ruling R166), with the body of the
  world's `Flower.MkMark.MarkInvariantBatchV` verbatim: every LF batch at unmarked vines of `𝒱` out of a `Clean`
  reconstruction carries the marking.  The world proves it for `markI0` with `Clean := True` and for `markI` with
  `StemCleanV`; main only consumes it.
* Coarse′ classes (`coarseStateMk`, twists at the unmarked vines of `𝒱`) are rebased at any member
  (`coarse_outputs_rebaseMk`) and are disjoint or equal (`coarse_outputs_disjoint_or_eqMk`), given the coarse
  transport `MarkInvariantBatchV mk fun _ => True`.  The proof runs the fine machinery at the all-`SG` prescription,
  whose unmarked `𝒱₀` is exactly `𝒱 ∖ Mk` (`vinesV0_allSG`).
* Fine′ classes (`BatchReach`/`Related` at `mk`) keep their output set (`Related.outputs_eqMk`) when every fine batch
  carries the marking (`FineTransportedAt`, from `MarkInvariantBatchV mk Clean` at clean points). -/
@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Stage1Mk
open WaveTurbulence.Stage1 WaveTurbulence.VineA

variable {w : ℕ}

/-- **Corrected Lemma 2⁺(a), batch form** (ruling R166; body of the world's `Flower.MkMark.MarkInvariantBatchV`,
verbatim): every family member is an unmarked vine of `𝒱`. -/
def MarkInvariantBatchV (mk : MarkFn w) (Clean : ∀ {LG : LayeredGarden w}, VineA.PrimeData LG → Prop) : Prop :=
  ∀ {p : ℕ} {kind : Bool} {ι : Type} {L : List ι} {A B : LFTwist.FamilyReconstruction w ι}
    (h : LFTwist.FamilyBatch p kind L A B) (hA : Reg.Skeleton.IsPrimeGarden A.skeleton),
    (∀ i, ∃ c ∈ vinesV A.skeleton, c.atoms = A.family.atoms i ∧
      c ∉ mk (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered)) →
    Clean (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered) →
    MarkTransported (VineA.batchMolIso h)
      (mk (⟨A.skeleton, hA, A.data, A.decodes⟩ : VineA.PrimeData A.layered))
      (mk (⟨B.skeleton, VineA.batch_prime h hA, B.data, B.decodes⟩ : VineA.PrimeData B.layered))

/-- The empty marking is invariant along every batch (main's Stage 1). -/
theorem markInvariantBatchV_empty (Clean : ∀ {LG : LayeredGarden w}, VineA.PrimeData LG → Prop) :
    MarkInvariantBatchV (fun _ => ∅) Clean :=
  fun h _ _ _ => markTransported_empty (VineA.batchMolIso h)

end WaveTurbulence.Stage1Mk

namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.Reg.Skeleton

variable {w p : ℕ} {kind : Bool} {LG LH : LayeredGarden w}

/-- At the all-`SG` prescription the unmarked `𝒱₀` is the unmarked carrier `𝒱 ∖ Mk` of the coarse′ state. -/
theorem vinesV0_allSG (G : Garden w) (Mk : Set (CLVine G)) :
    vinesV0 G (fun _ => .SG) Mk = {c | c ∈ vinesV G ∧ c ∉ Mk} := by
  ext c
  constructor
  · rintro ⟨hc, _, _, _, _, hcM⟩
    exact ⟨hc, hcM⟩
  · rintro ⟨hc, hcM⟩
    have hc' := hc
    obtain ⟨S, hS, hi, _⟩ := hc'
    exact ⟨hc, S, hS, hi, rfl, hcM⟩

/-- The coarse′ state is an exact selected family at the all-`SG` prescription. -/
theorem coarseStateMk_isV0Fam (A : PrimeData LG) (Mk : Set (CLVine A.skeleton)) :
    IsV0Fam (coarseStateMk A Mk).family (fun _ => .SG) Mk := by
  constructor
  · intro i
    have he : familyVine (coarseStateMk A Mk).family i = i.1 := clVine_eq_of_atoms rfl
    rw [he]
    exact (Set.ext_iff.mp (vinesV0_allSG A.skeleton Mk) i.1).mpr i.2.1
  · intro c hc hcore
    exact ⟨⟨c, (Set.ext_iff.mp (vinesV0_allSG A.skeleton Mk) c).mp hc, hcore⟩, rfl⟩

/-- The coarse′ outputs are the fine′ outputs at the all-`SG` prescription. -/
theorem coarseStateMk_outputs_allSG (A : PrimeData LG) (Mk : Set (CLVine A.skeleton)) :
    (coarseStateMk A Mk).allCoreOutputs (p := p) (kind := kind) =
      (A.fineState (fun _ => .SG) Mk).allCoreOutputs (p := p) (kind := kind) :=
  A.state_allCoreOutputs_congr (vinesV0_allSG A.skeleton Mk).symm _ _

/-- B1b-2 (Mk-general form of `PrimeData.coarse_outputs_rebase`): coarse′ output sets can be rebased at any member's
prime representative, when the coarse marking is carried by every batch (`MarkInvariantBatchV mk fun _ => True`; the
world's `markInvariantBatchV_markI0`). -/
theorem PrimeData.coarse_outputs_rebaseMk {mk : Stage1Mk.MarkFn w}
    (hV : Stage1Mk.MarkInvariantBatchV mk fun _ => True) (A : PrimeData LG) (B : PrimeData LH)
    (h : LH ∈ (coarseStateMk A (mk A)).allCoreOutputs (p := p) (kind := kind)) :
    (coarseStateMk A (mk A)).allCoreOutputs (p := p) (kind := kind) =
      (coarseStateMk B (mk B)).allCoreOutputs (p := p) (kind := kind) := by
  obtain ⟨C, ⟨L, hL, hbatch⟩, he⟩ := (congruent_layered_iff p kind (coarseStateMk A (mk A)) LH).mp h
  have hT := hV hbatch A.prime (fun i => ⟨i.1, i.2.1.1, rfl, i.2.1.2⟩) trivial
  have hr := fine_outputs_rebaseMk hbatch hL A.prime (fun _ => .SG) (coarseStateMk_isV0Fam A (mk A)) hT
  subst he
  have hr' : (coarseStateMk A (mk A)).allCoreOutputs (p := p) (kind := kind) =
      ((⟨C.skeleton, batch_prime hbatch A.prime, C.data, C.decodes⟩ : PrimeData C.layered).fineState
        (fun _ => .SG) (mk (⟨C.skeleton, batch_prime hbatch A.prime, C.data, C.decodes⟩ : PrimeData C.layered))).allCoreOutputs
        (p := p) (kind := kind) := hr
  rw [← coarseStateMk_outputs_allSG] at hr'
  have hu : (⟨C.skeleton, batch_prime hbatch A.prime, C.data, C.decodes⟩ : PrimeData C.layered) = B :=
    primeData_unique _ _
  rw [hu] at hr'
  exact hr'

/-- B1b-2 (Mk-general form of `PrimeData.coarse_outputs_disjoint_or_eq`). -/
theorem PrimeData.coarse_outputs_disjoint_or_eqMk {mk : Stage1Mk.MarkFn w}
    (hV : Stage1Mk.MarkInvariantBatchV mk fun _ => True) (A : PrimeData LG) (B : PrimeData LH) :
    Disjoint ((coarseStateMk A (mk A)).allCoreOutputs (p := p) (kind := kind))
      ((coarseStateMk B (mk B)).allCoreOutputs (p := p) (kind := kind)) ∨
    (coarseStateMk A (mk A)).allCoreOutputs (p := p) (kind := kind) =
      (coarseStateMk B (mk B)).allCoreOutputs (p := p) (kind := kind) := by
  classical
  by_cases hd : Disjoint ((coarseStateMk A (mk A)).allCoreOutputs (p := p) (kind := kind))
      ((coarseStateMk B (mk B)).allCoreOutputs (p := p) (kind := kind))
  · exact Or.inl hd
  · right
    obtain ⟨K, hKA, hKB⟩ := Set.not_disjoint_iff.mp hd
    have hpK : K.garden.IsPlain := by
      obtain ⟨C, _, he⟩ := (congruent_layered_iff p kind (coarseStateMk A (mk A)) K).mp hKA
      rw [← he]
      exact C.decodes.1
    let E := primeDataOf K hpK
    exact (A.coarse_outputs_rebaseMk hV E hKA).trans (B.coarse_outputs_rebaseMk hV E hKB).symm

namespace PrescribedPrimeGarden

/-- B1b-2: every fine′ batch out of `a` carries the fine marking `mk`. -/
def FineTransportedAt (mk : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) : Prop :=
  ∀ {p : ℕ} {kind : Bool} {L : List (CoreIndex (vinesV0 a.prime.skeleton a.totalSigma (mk a.prime)))}
    {B : FamilyReconstruction w (CoreIndex (vinesV0 a.prime.skeleton a.totalSigma (mk a.prime)))}
    (h : FamilyBatch p kind L (a.state mk) B),
    Stage1Mk.MarkTransported (batchMolIso h) (mk a.prime)
      (mk (⟨B.skeleton, batch_prime h a.prime.prime, B.data, B.decodes⟩ : PrimeData B.layered))

/-- The fine transport at a clean point, from the batch form of Lemma 2⁺(a). -/
theorem fineTransportedAt_of_markInvariantBatchV {mk : Stage1Mk.MarkFn w}
    {Clean : ∀ {LG : LayeredGarden w}, PrimeData LG → Prop} (hV : Stage1Mk.MarkInvariantBatchV mk Clean)
    (a : PrescribedPrimeGarden w) (hc : Clean a.prime) : a.FineTransportedAt mk :=
  fun h => hV h a.prime.prime (fun i => ⟨i.1, i.2.1.1, rfl, (mem_vinesV0.mp i.2.1).2⟩) hc

/-- B1b-2 (Mk-general form of `BatchReach.outputs_eq`): a fine′ batch edge keeps the fine′ output set. -/
theorem BatchReach.outputs_eqMk {mk : Stage1Mk.MarkFn w} {a b : PrescribedPrimeGarden w}
    (hT : a.FineTransportedAt mk) (h : BatchReach (p := p) (kind := kind) a b mk) :
    a.outputs (p := p) (kind := kind) mk = b.outputs (p := p) (kind := kind) mk := by
  obtain ⟨L, B, hb, hL, rfl⟩ := h
  have hr := fine_outputs_rebaseMk hb hL a.prime.prime a.totalSigma
    (fineState_isV0FamMk a.prime a.totalSigma) (hT hb)
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      extendGroupPrescription (transportGroupPrescription (batchMolIso hb) a.sigma) :=
    transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [ht] at hr
  exact hr

/-- B1b-2 (Mk-general form of `Related.outputs_eq`). -/
theorem Related.outputs_eqMk {mk : Stage1Mk.MarkFn w} (hT : ∀ c : PrescribedPrimeGarden w, c.FineTransportedAt mk)
    {a b : PrescribedPrimeGarden w} (h : Related (p := p) (kind := kind) a b mk) :
    a.outputs (p := p) (kind := kind) mk = b.outputs (p := p) (kind := kind) mk := by
  induction h with
  | rel _ _ h => exact BatchReach.outputs_eqMk (hT _) h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

/-- B1b-2 (Mk-general form of `mem_outputs_self`). -/
theorem mem_outputs_selfMk (mk : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    a.layered ∈ a.outputs (p := p) (kind := kind) mk := a.prime.mem_fine_outputs_selfMk a.totalSigma (mk a.prime)

/-- B1b-2 (Mk-general form of `tauClass_image`): exact garden projection of a fine′ class. -/
theorem tauClass_imageMk {mk : Stage1Mk.MarkFn w} (hT : ∀ c : PrescribedPrimeGarden w, c.FineTransportedAt mk)
    (a : PrescribedPrimeGarden w) :
    PrescribedPrimeGarden.layered '' a.tauClass (p := p) (kind := kind) mk = a.outputs (p := p) (kind := kind) mk := by
  ext LG
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [Related.outputs_eqMk hT hb]
    exact mem_outputs_selfMk mk b
  · intro hLG
    obtain ⟨B, ⟨L, hL, hb⟩, he⟩ := (congruent_layered_iff p kind (a.state mk) LG).mp hLG
    let b := ofState B (batch_prime hb a.prime.prime) (transportGroupPrescription (batchMolIso hb) a.sigma)
    exact ⟨b, Relation.EqvGen.rel a b ⟨L, B, hb, hL, rfl⟩, he⟩

/-- B1b-2: a fine′ batch edge stays inside the coarse′ class of its source (for a coarse marking below the fine one),
with no transport hypothesis on the fine marking. -/
theorem BatchReach.mem_coarseMk {mkF mkC : Stage1Mk.MarkFn w}
    (hsub : ∀ {LG : LayeredGarden w} (A : PrimeData LG), mkC A ⊆ mkF A) {a b : PrescribedPrimeGarden w}
    (h : BatchReach (p := p) (kind := kind) a b mkF) :
    b.layered ∈ (coarseStateMk a.prime (mkC a.prime)).allCoreOutputs (p := p) (kind := kind) := by
  obtain ⟨L, B, hb, hL, rfl⟩ := h
  exact a.prime.fine_outputs_subset_coarseMk a.totalSigma (hsub a.prime)
    ((congruent_layered_iff p kind (a.state mkF) B.layered).mpr ⟨B, ⟨L, hL, hb⟩, rfl⟩)

end PrescribedPrimeGarden
end WaveTurbulence.VineA
