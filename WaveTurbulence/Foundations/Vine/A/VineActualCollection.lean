/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VinePlainA4
public import WaveTurbulence.Foundations.Vine.A.VineSpliceDecorationLift
/-! Actual successor collection geometry and hinge semantics on every spliced decoration. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LGSpine LFTwist
variable {w p d : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- Full C1 support names in the literal common normalized garden. -/
noncomputable def collectionAddressSupports (G : Garden w) (σ : Prescription G) :
    Finset (Finset (Fin w × TTree.Path)) := by
  classical
  exact ((NormalizedSplice.objects G σ).map (fun O => O.atoms.image Subtype.val)).toFinset

/-- The independently chosen C1 lists have identical support sets in literal normalized coordinates. -/
theorem BatchIso.collectionAddressSupports (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    VineA.collectionAddressSupports B.skeleton (transportPrescription F σ) =
      VineA.collectionAddressSupports A.skeleton σ := by
  classical
  have hp := (NormalizedSplice.BatchIso.objects_atoms_perm h σ hA).map
    (fun S => S.image (fun b : GBranch (stSt B.skeleton (transportPrescription F σ)).G.tree => b.1))
  have he (O : SourceVine.Object (stSt A.skeleton σ).G.molecule) :
      ((h.spliceMolIso σ hA).img O.atoms).image Subtype.val = O.atoms.image Subtype.val := by
    calc
      _ = O.atoms.image (fun b : GBranch (stSt A.skeleton σ).G.tree => ((h.spliceMolIso σ hA).e b).1) :=
        Finset.image_image
      _ = _ := Finset.image_congr fun b _ => h.spliceMolIso_address σ hA b
  have hm : (fun O : SourceVine.Object (stSt A.skeleton σ).G.molecule =>
      ((h.spliceMolIso σ hA).img O.atoms).image (fun b : GBranch (stSt B.skeleton (transportPrescription F σ)).G.tree => b.1)) =
      (fun O => O.atoms.image (fun b : GBranch (stSt A.skeleton σ).G.tree => b.1)) := funext he
  simp only [List.map_map, Function.comp_def] at hp
  rw [hm] at hp
  apply Finset.ext
  intro S
  change S ∈ ((NormalizedSplice.objects B.skeleton (transportPrescription F σ)).map
      (fun O => O.atoms.image (fun b : GBranch (stSt B.skeleton (transportPrescription F σ)).G.tree => b.1))).toFinset ↔
    S ∈ ((NormalizedSplice.objects A.skeleton σ).map
      (fun O => O.atoms.image (fun b : GBranch (stSt A.skeleton σ).G.tree => b.1))).toFinset
  rw [List.mem_toFinset, List.mem_toFinset]
  exact hp.mem_iff.symm

/-- The actual first/second choices have equal gap kinds on every genuine quotient decoration. -/
theorem BatchIso.actual_hinge_gapKind (h : BatchIso p kind L A B F)
    (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ)
    (v : GBranch (stSt A.skeleton σ).G.tree) (hv : v ∈ (NormalizedSplice.collectionChoices A.skeleton σ).hinges)
    {scale : ℝ} (hscale : scale ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt B.skeleton (transportPrescription F σ)).G d roots 0) :
    ∃ x y u t,
      (NormalizedSplice.collectionChoices A.skeleton σ).first v = some x ∧
      (NormalizedSplice.collectionChoices A.skeleton σ).second v = some y ∧
      (NormalizedSplice.collectionChoices B.skeleton (transportPrescription F σ)).first ((h.spliceMolIso σ hA).e v) = some u ∧
      (NormalizedSplice.collectionChoices B.skeleton (transportPrescription F σ)).second ((h.spliceMolIso σ hA).e v) = some t ∧
      Molecule.gapKind scale γ η
        (Molecule.gapAt scale base (bondIndex (stSt B.skeleton (transportPrescription F σ)).G z.1 ∘
          (h.spliceMolIso σ hA).d) x y) =
      Molecule.gapKind scale γ η
        (Molecule.gapAt scale base (bondIndex (stSt B.skeleton (transportPrescription F σ)).G z.1) u t) := by
  obtain ⟨κ, hlab⟩ := splice_labels_extend B.plain (transportPrescription F σ) hscale base roots z
  exact NormalizedSplice.BatchIso.collectionChoices_hinge_gapKind h σ hA v hv scale γ η base
    _ (bondIndex B.skeleton κ.1) (spliced_molecule_decoration B.skeleton B.plain hscale base roots κ)
    (fun b _ hb => gardenSource_eq_zero_of_deg_four B.skeleton B.plain _ b hb)
    _ hlab

end WaveTurbulence.VineA
