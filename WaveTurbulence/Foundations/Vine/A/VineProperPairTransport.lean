/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchUnitJoints
public import WaveTurbulence.Foundations.Vine.A.VineTripleAtTransport
/-! The literal proper-pair predicate transports along actual selected batches. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- An actual proper pair belongs to the hinge which is its unit's crown. -/
theorem properPair_mem_hinges {G : Garden w} {σ : Prescription G} {v : GBranch (stSt G σ).G.tree}
    {x y : GardenDart (stSt G σ).G} (h : ProperPair G σ v x y) : v ∈ (stSt G σ).hinges := by
  obtain ⟨_, u, hu, hc, _⟩ := h
  apply ((stSt G σ).mem_hinges v).mpr
  rw [hc, stSt_cls_mem (Mole.garden_isMolecule G) σ hu u.isBlock.2.1]
  exact Option.some_ne_none _

/-- Actual support/joint transport and old dart names carry any actual proper hinge pair. -/
theorem BatchIso.properPair_image (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) {v : GBranch (stSt A.skeleton σ).G.tree}
    {x y : GardenDart (stSt A.skeleton σ).G} (hP : ProperPair A.skeleton σ v x y) :
    ProperPair B.skeleton (transportPrescription F σ) ((h.spliceMolIso σ hA).e v)
      ((h.spliceMolIso σ hA).d x) ((h.spliceMolIso σ hA).d y) := by
  obtain ⟨hT, u, hu, hc, j, hj, hx, hy, hnx, hny⟩ := hP
  obtain ⟨t, ht, ha, htu, htl⟩ := h.units_joints σ hA hu
  refine ⟨tripleAt_image (h.spliceMolIso σ hA) hT, t, ht, ?_, F.e j, ?_, ?_, ?_, ?_, ?_⟩
  · exact (h.spliceMolIso_branch_names σ hA v).trans ((congrArg F.e hc).trans htu.symm)
  · rcases hj with rfl | rfl
    · exact Or.inl htu.symm
    · exact Or.inr htl.symm
  · rw [h.spliceMolIso_dart_names σ hA x, F.atom_comm, hx]
  · rw [h.spliceMolIso_dart_names σ hA y, F.atom_comm, hy]
  · intro hn
    rw [ha, h.spliceMolIso_dart_names σ hA x] at hn
    exact hnx ((F.inGroup_img u.atoms _).mp hn)
  · intro hn
    rw [ha, h.spliceMolIso_dart_names σ hA y] at hn
    exact hny ((F.inGroup_img u.atoms _).mp hn)

end WaveTurbulence.VineA
