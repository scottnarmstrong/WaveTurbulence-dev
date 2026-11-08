/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePieceProfile
public import WaveTurbulence.Foundations.Vine.A.VinePlainTauPartition
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedCollectionGeometry
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedHingeGapTransport
public import WaveTurbulence.Foundations.Vine.A.VineMarkedClasses
/-! Complete A4 kernel-relevant profiles on the actual fixed-sigma plain-garden classes. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist LGSpine
variable {R p : ℕ} {kind : Bool}

/-- The successor producer piece at the unique prime representative of a plain garden. -/
noncomputable def normalizedPiece (a : PrescribedPrimeGarden (2 * R)) (d : ℕ)
    (Mk : Set (Stage1.CLVine a.prime.skeleton) := ∅) :=
  NormalizedSplice.stage1PieceOf d a.prime.prime.1 a.layered a.prime.decodes a.totalSigma Mk

/-- The actual normalized garden, layers, hinges, counts and entire gap functional. -/
noncomputable def profile (a : PrescribedPrimeGarden (2 * R)) : PieceProfile (2 * R) :=
  familyPieceProfile a.state a.totalSigma

/-- B1b-3 (Mk-general form of `profile`): the piece profile (gap functional, layers, hinges, counts) of the fine′
state at the marking `mk`. -/
noncomputable def profileMk (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) : PieceProfile (2 * R) :=
  familyPieceProfileMk (a.state mk) a.totalSigma (mk a.prime)

/-- B1b-3 (Mk-general form of `BatchReach.profile_eq`): fine′ batch edges preserve the piece profile at `mk`, given
the fine transport of the marking and B2c's dart-label gap identity. -/
theorem BatchReach.profile_eqMk {mk : Stage1Mk.MarkFn (2 * R)} {a b : PrescribedPrimeGarden (2 * R)}
    (hT : a.FineTransportedAt mk) (hg : GapValueSelDartsMk (2 * R))
    (h : BatchReach (p := p) (kind := kind) a b mk) : b.profileMk mk = a.profileMk mk := by
  obtain ⟨L, B, hb, _, rfl⟩ := h
  have he := (batchMolIso_spec hb).pieceProfileMk a.totalSigma (hT hb) (fineState_isV0FamMk a.prime a.totalSigma) hg
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      extendGroupPrescription (transportGroupPrescription (batchMolIso hb) a.sigma) :=
    transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [ht] at he
  exact he

/-- B1b-3 (Mk-general form of `Related.profile_eq`). -/
theorem Related.profile_eqMk {mk : Stage1Mk.MarkFn (2 * R)}
    (hT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mk) (hg : GapValueSelDartsMk (2 * R))
    {a b : PrescribedPrimeGarden (2 * R)} (h : Related (p := p) (kind := kind) a b mk) :
    b.profileMk mk = a.profileMk mk := by
  induction h with
  | rel _ _ h => exact BatchReach.profile_eqMk (hT _) hg h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact hj.trans ih

/-- Actual batch edges preserve all kernel-relevant successor piece fields. -/
theorem BatchReach.profile_eq {a b : PrescribedPrimeGarden (2 * R)}
    (h : BatchReach (p := p) (kind := kind) a b) : b.profile = a.profile := by
  obtain ⟨L, B, hb, _, rfl⟩ := h
  have he := (batchMolIso_spec hb).pieceProfile a.totalSigma (fineState_isV0Fam a.prime a.totalSigma)
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      extendGroupPrescription (transportGroupPrescription (batchMolIso hb) a.sigma) :=
    transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [ht] at he
  exact he

/-- Full A4 profiles are constant along fine tau equivalence, including reverse traces. -/
theorem Related.profile_eq {a b : PrescribedPrimeGarden (2 * R)}
    (h : Related (p := p) (kind := kind) a b) : b.profile = a.profile := by
  induction h with
  | rel _ _ h => exact h.profile_eq
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact hj.trans ih

/-- A4 for the uniquely identified fixed-sigma representative of every actual garden output. -/
theorem plainTau_profile_eq {a b : PrescribedPrimeGarden (2 * R)}
    (hσ : b.code = a.code) (h : b.layered ∈ a.outputs (p := p) (kind := kind)) : b.profile = a.profile := by
  obtain ⟨c, hc, he⟩ := (Set.ext_iff.mp (tauClass_image a) b.layered).mpr h
  have hcb : c = b := eq_of_layered_code he ((Related.code_eq hc).symm.trans hσ.symm)
  subst b
  exact Related.profile_eq hc

/-- Every fixed-sigma tau class carries one actual full A4 profile. -/
theorem plainTau_constant_profile (a : PrescribedPrimeGarden (2 * R))
    {T : Set (LayeredGarden (2 * R))} (hT : T ∈ a.plainTauClasses (p := p) (kind := kind)) :
    ∃ P : PieceProfile (2 * R), ∀ b ∈ a.fixedSigmaPoints (p := p) (kind := kind),
      b.layered ∈ T → b.profile = P := by
  obtain ⟨c, hc, rfl⟩ := hT
  refine ⟨c.profile, ?_⟩
  intro b hb hL
  exact plainTau_profile_eq (hb.2.trans hc.2.symm) hL

/-- S2's representative piece has exactly the garden carried by the common profile. -/
theorem normalizedPiece_garden (a : PrescribedPrimeGarden (2 * R)) (d : ℕ) :
    (a.normalizedPiece d).Gsb = a.profile.gap.garden := rfl

theorem normalizedPiece_layer (a : PrescribedPrimeGarden (2 * R)) (d : ℕ) :
    (a.normalizedPiece d).layer = a.profile.layer := rfl

theorem normalizedPiece_hinges (a : PrescribedPrimeGarden (2 * R)) (d : ℕ) :
    (a.normalizedPiece d).Cs.hinges = a.profile.hinges := rfl

theorem normalizedPiece_counts (a : PrescribedPrimeGarden (2 * R)) (d : ℕ) :
    (a.normalizedPiece d).gsk = a.profile.gsk ∧ (a.normalizedPiece d).bsk = a.profile.bsk := ⟨rfl, rfl⟩

end WaveTurbulence.VineA.PrescribedPrimeGarden
