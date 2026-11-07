/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineActualCollection
public import WaveTurbulence.Foundations.Vine.A.VineActualKernel
/-! S2 producer exports: fixed-sigma A4 including actual C1 supports and counts. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist

/-- A4's kernel profile together with the entire actual C1 support set and its actual index count. -/
structure FullA4Profile (w : ℕ) where
  piece : PieceProfile w
  collection : Finset (Finset (Fin w × TTree.Path))
  count : ℕ

namespace PrescribedPrimeGarden
variable {R p : ℕ} {kind : Bool}

/-- Full data of the actual successor piece, independent of a trace or representative choices. -/
noncomputable def fullProfile (a : PrescribedPrimeGarden (2 * R)) : FullA4Profile (2 * R) :=
  ⟨a.profile, collectionAddressSupports a.prime.skeleton a.totalSigma, (a.normalizedPiece 0).Cs.count⟩

/-- Every actual fine batch preserves all the exported A4 data. -/
theorem BatchReach.fullProfile_eq {a b : PrescribedPrimeGarden (2 * R)}
    (h : BatchReach (p := p) (kind := kind) a b) : b.fullProfile = a.fullProfile := by
  have hP := h.profile_eq
  obtain ⟨L, B, hb, _, rfl⟩ := h
  have hC := (batchMolIso_spec hb).collectionAddressSupports a.totalSigma (fineState_isV0Fam a.prime a.totalSigma)
  have hN := NormalizedSplice.BatchIso.collectionChoices_count (batchMolIso_spec hb)
    a.totalSigma (fineState_isV0Fam a.prime a.totalSigma)
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      extendGroupPrescription (transportGroupPrescription (batchMolIso hb) a.sigma) :=
    transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [ht] at hC hN
  change FullA4Profile.mk _ _ _ = FullA4Profile.mk _ _ _
  congr 1
  exact hN.symm

/-- Full A4 data are constant on every prescribed fine tau class. -/
theorem Related.fullProfile_eq {a b : PrescribedPrimeGarden (2 * R)}
    (h : Related (p := p) (kind := kind) a b) : b.fullProfile = a.fullProfile := by
  induction h with
  | rel _ _ h => exact h.fullProfile_eq
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact hj.trans ih

/-- Full A4 on plain gardens with the source's fixed coloring of all maximal groups. -/
theorem plainTau_fullA4 {a b : PrescribedPrimeGarden (2 * R)}
    (hσ : b.code = a.code) (h : b.layered ∈ a.outputs (p := p) (kind := kind)) :
    b.fullProfile = a.fullProfile := by
  obtain ⟨c, hc, he⟩ := (Set.ext_iff.mp (tauClass_image a) b.layered).mpr h
  have hcb : c = b := eq_of_layered_code he ((Related.code_eq hc).symm.trans hσ.symm)
  subst b
  exact Related.fullProfile_eq hc

/-- The producer gets a unique prescribed representative, with all A4 data, for every actual class member. -/
theorem fullA4_at_garden (a : PrescribedPrimeGarden (2 * R)) {LG : LayeredGarden (2 * R)}
    (h : LG ∈ a.outputs (p := p) (kind := kind)) :
    ∃! b : PrescribedPrimeGarden (2 * R), b.layered = LG ∧ b.code = a.code ∧ b.fullProfile = a.fullProfile := by
  obtain ⟨b, hb, he⟩ := (Set.ext_iff.mp (tauClass_image a) LG).mpr h
  refine ⟨b, ⟨he, (Related.code_eq hb).symm, Related.fullProfile_eq hb⟩, ?_⟩
  intro c hc
  exact eq_of_layered_code (hc.1.trans he.symm) (hc.2.1.trans (Related.code_eq hb))

/-- Each fixed-sigma tau class carries one full A4 profile. -/
theorem plainTau_constant_fullProfile (a : PrescribedPrimeGarden (2 * R))
    {T : Set (LayeredGarden (2 * R))} (hT : T ∈ a.plainTauClasses (p := p) (kind := kind)) :
    ∃ P : FullA4Profile (2 * R), ∀ b ∈ a.fixedSigmaPoints (p := p) (kind := kind),
      b.layered ∈ T → b.fullProfile = P := by
  obtain ⟨c, hc, rfl⟩ := hT
  exact ⟨c.fullProfile, fun b hb hL => plainTau_fullA4 (hb.2.trans hc.2.symm) hL⟩

end PrescribedPrimeGarden
end WaveTurbulence.VineA
