/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchSplice
/-! Actual layer, hinge and counting fields of Stage 1 pieces along selected batches. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LFTwist
variable {R p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction (2 * R) ι}
variable {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Actual piece layers commute with the actual full batch quotient map. -/
theorem BatchIso.piece_layer (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (d : ℕ) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)).layer
        ((h.spliceMolIso σ hA).e c) =
      (stage1PieceOf d A.plain A.layered A.decodes σ).layer c :=
  (congrArg (RegRed.coreLayer B.layered B.data B.plain B.decodes)
    (h.spliceMolIso_branch_names σ hA c)).trans (h.coreLayer ((stSt A.skeleton σ).M.ob c))

/-- The actual constructed hinge membership follows the actual batch map. -/
theorem BatchIso.piece_hinge_iff (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (d : ℕ) (c : GBranch (stSt A.skeleton σ).G.tree) :
    (h.spliceMolIso σ hA).e c ∈
        (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)).Cs.hinges ↔
      c ∈ (stage1PieceOf d A.plain A.layered A.decodes σ).Cs.hinges := by
  let S := stSt A.skeleton σ
  let T := stSt B.skeleton (transportPrescription F σ)
  have he : T.cls (T.M.ob ((h.spliceMolIso σ hA).e c)) = (S.cls (S.M.ob c)).map F.e :=
    (congrArg T.cls (h.spliceMolIso_branch_names σ hA c)).trans (h.splice_classes σ hA (S.M.ob c))
  have hn : ((S.cls (S.M.ob c)).map F.e ≠ none) ↔ S.cls (S.M.ob c) ≠ none := by
    cases S.cls (S.M.ob c) <;> simp
  exact (T.mem_hinges _).trans
    ((Iff.of_eq (congrArg (fun o : Option (GBranch B.skeleton.tree) => o ≠ none) he)).trans
      (hn.trans (S.mem_hinges c).symm))

/-- The actual full hinge sets of the constructed pieces correspond. -/
theorem BatchIso.piece_hinges (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (d : ℕ) :
    (stage1PieceOf d A.plain A.layered A.decodes σ).Cs.hinges.image (h.spliceMolIso σ hA).e =
      (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)).Cs.hinges := by
  ext y
  obtain ⟨x, rfl⟩ := (h.spliceMolIso σ hA).e.surjective y
  constructor
  · intro hy
    obtain ⟨c, hc, he⟩ := Finset.mem_image.mp hy
    exact (h.piece_hinge_iff σ hA d x).mpr ((h.spliceMolIso σ hA).e.injective he ▸ hc)
  · intro hy
    exact Finset.mem_image.mpr ⟨x, (h.piece_hinge_iff σ hA d x).mp hy, rfl⟩

/-- The actual constructed bsk follows every selected batch. -/
theorem BatchIso.piece_bsk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (d : ℕ) :
    (stage1PieceOf d B.plain B.layered B.decodes (transportPrescription F σ)).bsk =
      (stage1PieceOf d A.plain A.layered A.decodes σ).bsk := h.badCount σ hA

end WaveTurbulence.VineA
