/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedPartition
public import WaveTurbulence.Foundations.Vine.A.VineBatchPieceData
/-! The actual piece indices are constant on prescribed fine tau classes. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist
variable {R p : ℕ} {kind : Bool}

/-- The actual independently constructed piece at a prescribed prime garden. -/
noncomputable def piece (a : PrescribedPrimeGarden (2 * R)) (d : ℕ) :=
  stage1PieceOf d a.prime.prime.1 a.layered a.prime.decodes a.totalSigma

/-- Actual prescribed batch edges preserve the actual gsk field. -/
theorem BatchReach.piece_gsk {a b : PrescribedPrimeGarden (2 * R)}
    (h : BatchReach (p := p) (kind := kind) a b) (d : ℕ) : (b.piece d).gsk = (a.piece d).gsk := by
  obtain ⟨L, B, hb, _, rfl⟩ := h
  have hr := (batchMolIso_spec hb).piece_gsk a.totalSigma (fineState_isV0Fam a.prime a.totalSigma) d
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      extendGroupPrescription (transportGroupPrescription (batchMolIso hb) a.sigma) :=
    transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [ht] at hr
  exact hr

/-- Actual prescribed batch edges preserve the actual bsk field. -/
theorem BatchReach.piece_bsk {a b : PrescribedPrimeGarden (2 * R)}
    (h : BatchReach (p := p) (kind := kind) a b) (d : ℕ) : (b.piece d).bsk = (a.piece d).bsk := by
  obtain ⟨L, B, hb, _, rfl⟩ := h
  have hr := (batchMolIso_spec hb).piece_bsk a.totalSigma (fineState_isV0Fam a.prime a.totalSigma) d
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      extendGroupPrescription (transportGroupPrescription (batchMolIso hb) a.sigma) :=
    transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [ht] at hr
  exact hr

/-- Full actual gsk is constant on each prescribed fine tau class. -/
theorem Related.piece_gsk {a b : PrescribedPrimeGarden (2 * R)}
    (h : Related (p := p) (kind := kind) a b) (d : ℕ) : (b.piece d).gsk = (a.piece d).gsk := by
  induction h with
  | rel _ _ h => exact h.piece_gsk d
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact hj.trans ih

/-- Full actual bsk is constant on each prescribed fine tau class. -/
theorem Related.piece_bsk {a b : PrescribedPrimeGarden (2 * R)}
    (h : Related (p := p) (kind := kind) a b) (d : ℕ) : (b.piece d).bsk = (a.piece d).bsk := by
  induction h with
  | rel _ _ h => exact h.piece_bsk d
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact hj.trans ih

end WaveTurbulence.VineA.PrescribedPrimeGarden
