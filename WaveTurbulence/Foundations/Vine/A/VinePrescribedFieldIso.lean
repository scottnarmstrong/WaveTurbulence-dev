/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePrescribedIndices
public import WaveTurbulence.Foundations.Vine.A.VinePieceFieldIso
/-! Actual basic piece fields correspond throughout a prescribed fine tau class. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA.PrescribedPrimeGarden
open Stage1 RedSplice LFTwist
variable {R p : ℕ} {kind : Bool}

/-- An actual prescribed batch identifies the actual layer, hinges and counts. -/
theorem BatchReach.pieceFieldIso {a b : PrescribedPrimeGarden (2 * R)}
    (h : BatchReach (p := p) (kind := kind) a b) (d : ℕ) :
    Nonempty (PieceFieldIso (a.piece d) (b.piece d)) := by
  obtain ⟨L, B, hb, _, rfl⟩ := h
  have hi := (batchMolIso_spec hb).pieceFieldIso (d := d) a.totalSigma (fineState_isV0Fam a.prime a.totalSigma)
  have ht : transportPrescription (batchMolIso hb) a.totalSigma =
      extendGroupPrescription (transportGroupPrescription (batchMolIso hb) a.sigma) :=
    transport_extendGroupPrescription (batchMolIso hb) a.sigma
  rw [ht] at hi
  exact ⟨hi⟩

/-- Every two prescribed points in one fine tau class have an actual basic-piece isomorphism.
The remaining collection choices and gap specifications are not fields of this record. -/
theorem Related.pieceFieldIso {a b : PrescribedPrimeGarden (2 * R)}
    (h : Related (p := p) (kind := kind) a b) (d : ℕ) :
    Nonempty (PieceFieldIso (a.piece d) (b.piece d)) := by
  induction h with
  | rel _ _ h => exact h.pieceFieldIso d
  | refl a => exact ⟨PieceFieldIso.refl (a.piece d)⟩
  | symm _ _ _ ih =>
    obtain ⟨hi⟩ := ih
    exact ⟨hi.symm⟩
  | trans _ _ _ _ _ ih hj =>
    obtain ⟨hi⟩ := ih
    obtain ⟨hj⟩ := hj
    exact ⟨hi.trans hj⟩

/-- Every actual garden output has a prescribed representative with corresponding actual basic piece fields. -/
theorem pieceFieldIso_at_member (a : PrescribedPrimeGarden (2 * R)) (d : ℕ)
    (LG : LayeredGarden (2 * R)) (h : LG ∈ a.outputs (p := p) (kind := kind)) :
    ∃ b : PrescribedPrimeGarden (2 * R), b.layered = LG ∧ Related (p := p) (kind := kind) a b ∧
      Nonempty (PieceFieldIso (a.piece d) (b.piece d)) := by
  have hi : LG ∈ PrescribedPrimeGarden.layered '' a.tauClass (p := p) (kind := kind) := by
    rw [tauClass_image]
    exact h
  obtain ⟨b, hb, he⟩ := hi
  exact ⟨b, he, hb, Related.pieceFieldIso hb d⟩

end WaveTurbulence.VineA.PrescribedPrimeGarden
