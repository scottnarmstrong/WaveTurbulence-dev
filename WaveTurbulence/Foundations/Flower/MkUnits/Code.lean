/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.Defs
public import WaveTurbulence.Foundations.Stage1.Represents.RepVD7

/-! # MK-UNITS: the prescribed point of a run-class member at a marking

Main's code argument (`Vine/A/VinePrescribedCode`, `Stage1/Represents/RepVC3`, RepVD7) is stated at the empty marking:
its batch lemma `BatchIso.fine_coarseAtomWord` asks for the exact `𝒱₀` family.  The per-operation step uses only that
the twisted member is a vine of `𝒱` (`operation_fine_coarseAtomWord`), so it holds for the fine′ family of unmarked
`𝒱₀` vines and for the run family (`unitsFamily_isV0FamMk`), carrying an image marking along the batch.

* `BatchIso.fine_coarseAtomWordMk`, `Related.code_eqMk`: fine′ batches preserve the code.
* `memberPointMk`, `memberPoint_codeMk`, `memberPoint_relatedMk`: a member of the run class at `mk` carries a prescribed
  point fine′-related to the representative.
* `selPMk_iff_related`: the selection of a fine′ piece at a garden is the selection of any related point over it.

Adapted from main's `VineCoarseWordBatch.lean`, `VinePrescribedCode.lean`, `RepVC3.lean`, `RepVD7.lean` (see
`COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.MkUnits
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.LFTwist WaveTurbulence.VineA
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign WaveTurbulence.VineC WaveTurbulence.Represents
  WaveTurbulence.LGSpine

variable {w p : ℕ} {kind : Bool} {ι : Type*}

/-- The image of a marked vine set under a molecule isomorphism. -/
def imageMark {S S' : Garden w} (F : MolIso S.molecule S'.molecule) (M : Set (CLVine S)) : Set (CLVine S') :=
  {c' | ∃ c ∈ M, c'.atoms = F.img c.atoms}

/-- An isomorphism carries every marked set to its image marking. -/
theorem markTransported_imageMark {S S' : Garden w} (F : MolIso S.molecule S'.molecule) (M : Set (CLVine S)) :
    Stage1Mk.MarkTransported F M (imageMark F M) := by
  intro c c' h
  constructor
  · intro hc
    exact ⟨c, hc, h⟩
  · rintro ⟨c0, hc0, h0⟩
    have he : c0.atoms = c.atoms := F.img_injective (h0.symm.trans h)
    rw [← clVine_eq_of_atoms he]
    exact hc0

/-- Fine operations of an unmarked selected family preserve every coarse atom word (main's
`operation_fine_coarseAtomWord`, verbatim proof, at a marking). -/
theorem operation_fine_coarseAtomWordMk {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hF : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i) (v : GBranch A.skeleton.tree) :
    coarseAtomWord op.output.skeleton ((operationMolIso op).e v) = coarseAtomWord A.skeleton v := by
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · rfl
    · exact coarseAtomWord_twist (selectedMemberSite hF i)
        ⟨familyVine A.family i, mem_allSG (hF.1 i).1, rfl⟩ v

/-- Fold the fine operation maps of an unmarked selected family (main's `BatchIso.fine_coarseAtomWord` at a
marking; the marking is carried by its image). -/
theorem BatchIso.fine_coarseAtomWordMk {A B : FamilyReconstruction w ι} {L : List ι}
    {F : MolIso A.skeleton.molecule B.skeleton.molecule} (h : BatchIso p kind L A B F) :
    ∀ (σ : Prescription A.skeleton) (Mk : Set (CLVine A.skeleton)), IsV0Fam A.family σ Mk →
      ∀ v : GBranch A.skeleton.tree, coarseAtomWord B.skeleton (F.e v) = coarseAtomWord A.skeleton v := by
  induction h with
  | nil => intro _ _ _ _; rfl
  | skip _ _ ih => exact ih
  | apply op _ ih =>
    intro σ Mk hA v
    exact (ih _ _ (isV0Fam_operationMk hA op (markTransported_imageMark _ Mk)) ((operationMolIso op).e v)).trans
      (operation_fine_coarseAtomWordMk hA op v)

/-- Fine′ batch edges preserve the whole color graph. -/
theorem BatchReach.code_eqMk {mk : Stage1Mk.MarkFn w} {a b : PrescribedPrimeGarden w}
    (h : BatchReach (p := p) (kind := kind) a b mk) : a.code = b.code := by
  obtain ⟨L, B, hb, _, rfl⟩ := h
  exact (codedPrescription_map (batchMolIso hb)
    (BatchIso.fine_coarseAtomWordMk (batchMolIso_spec hb) a.totalSigma (mk a.prime)
      (fineState_isV0FamMk a.prime a.totalSigma)) a.sigma).symm

/-- Fine′ relatedness preserves the code. -/
theorem Related.code_eqMk {mk : Stage1Mk.MarkFn w} {a b : PrescribedPrimeGarden w}
    (h : Related (p := p) (kind := kind) a b mk) : a.code = b.code := by
  induction h with
  | rel _ _ h => exact BatchReach.code_eqMk h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

/-- The prescribed point carried by a member of the run class at `mk` along a full batch. -/
noncomputable def memberPointMk (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w)
    (y : UState w (unitsSplit (sourceAssemblyMk a mk))) (M : List (UnitsIndex (sourceAssemblyMk a mk)))
    (hr : ReachU p kind (unitsSplit (sourceAssemblyMk a mk)).Q M (sourceStart a mk) (sourceUnitsMk a mk) y.1 y.2) :
    PrescribedPrimeGarden w :=
  ⟨y.1.layered, ⟨y.1.skeleton, VineA.batch_prime hr.batch a.prime.prime, y.1.data, y.1.decodes⟩,
    transportGroupPrescription (batchMolIso hr.batch) a.sigma⟩

theorem memberPoint_codeMk (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w)
    (y : UState w (unitsSplit (sourceAssemblyMk a mk))) (M : List (UnitsIndex (sourceAssemblyMk a mk)))
    (hr : ReachU p kind (unitsSplit (sourceAssemblyMk a mk)).Q M (sourceStart a mk) (sourceUnitsMk a mk) y.1 y.2) :
    (memberPointMk a mk y M hr).code = a.code :=
  codedPrescription_map (batchMolIso hr.batch)
    (BatchIso.fine_coarseAtomWordMk (batchMolIso_spec hr.batch) a.totalSigma (mk a.prime)
      (unitsFamily_isV0FamMk (Mole.garden_isMolecule _) a.totalSigma)) a.sigma

theorem sourceClass_mem_outputsMk (a : PrescribedPrimeGarden w) (mk : Stage1Mk.MarkFn w)
    (y : UState w (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk) :
    y.1.layered ∈ a.outputs (p := p) (kind := kind) mk := by
  obtain ⟨M, hM, hr⟩ := member_traceMk a mk y hy
  rw [prescribed_outputs_eq_unitsStartMk a mk (sourceLayer a) (sourceLayer_isLayering a)
    (sourceLayer_reconstructs a)]
  exact ⟨M, y.1, hM, hr.batch, rfl⟩

/-- The member's prescribed point is fine′-related to the representative (main's `memberPoint_related'` at a
marking).  The run class is at the units marking `mkU`, the fine′ relation at the class marking `mkF`; they have the
same fine′ outputs (`hout`), and the fine transport `hFT` of `mkF` gives the tau-class image. -/
theorem memberPoint_relatedMk {mkF mkU : Stage1Mk.MarkFn w}
    (hFT : ∀ c : PrescribedPrimeGarden w, c.FineTransportedAt mkF) (a : PrescribedPrimeGarden w)
    (hout : a.outputs (p := p) (kind := kind) mkU = a.outputs (p := p) (kind := kind) mkF)
    (y : UState w (unitsSplit (sourceAssemblyMk a mkU))) (hy : y ∈ sourceClass a p kind mkU)
    (M : List (UnitsIndex (sourceAssemblyMk a mkU)))
    (hr : ReachU p kind (unitsSplit (sourceAssemblyMk a mkU)).Q M (sourceStart a mkU) (sourceUnitsMk a mkU) y.1 y.2) :
    Related (p := p) (kind := kind) a (memberPointMk a mkU y M hr) mkF := by
  have hmem := sourceClass_mem_outputsMk a mkU y hy
  rw [hout] at hmem
  obtain ⟨c, hc, hce⟩ := (Set.ext_iff.mp (tauClass_imageMk hFT a) y.1.layered).mpr hmem
  have hcode : c.code = (memberPointMk a mkU y M hr).code :=
    (Related.code_eqMk hc).symm.trans (memberPoint_codeMk a mkU y M hr).symm
  have he : c = memberPointMk a mkU y M hr := eq_of_layered_code hce hcode
  rw [← he]
  exact hc

/-- The selection of a fine′ piece at `LG` is the selection of any related prescribed point over `LG` (main's
`selP_iff_related` at a marking). -/
theorem selPMk_iff_related {R : ℕ} {A : Finset (LayeredGarden (2 * R))} {mk : Stage1Mk.MarkFn (2 * R)}
    (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (π : PcA R p kind A mk)
    (b : PrescribedPrimeGarden (2 * R)) (hb : Related (p := p) (kind := kind) (repPt π) b mk)
    (LG : LayeredGarden (2 * R)) (hLG : b.layered = LG) (κ : GenDecoration LG.garden P.d roots 0) :
    selPMk p kind A P base roots mk π LG κ ↔ selAt P base b.prime b.sigma (hLG ▸ κ) := by
  constructor
  · rintro ⟨b', h', hrel', hs'⟩
    have hcode : b'.code = b.code := (Related.code_eqMk hrel').symm.trans (Related.code_eqMk hb)
    have he : b' = b := eq_of_layered_code (h'.trans hLG.symm) hcode
    subst he
    subst hLG
    exact hs'
  · intro hs
    exact ⟨b, hLG, hb, hs⟩

end WaveTurbulence.Flower.MkUnits
