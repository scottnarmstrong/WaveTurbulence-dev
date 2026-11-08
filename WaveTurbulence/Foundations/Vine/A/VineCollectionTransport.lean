/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCollectionNormalForm
/-! Actual collection supports and Cs counts transport along selected LF batches. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine LFTwist
variable {w p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
variable {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}

/-- The contributing list carries exactly the actual maximal SG groups with a residual object. -/
theorem mem_contributingGroups {G : Garden w} (σ : Prescription G) (S : Finset (GBranch G.tree)) :
    S ∈ contributingGroups G σ ↔ S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ HasObj G S := by
  classical
  simp only [contributingGroups, List.mem_filter, decide_eq_true_eq, mem_sgGroups, and_assoc]

theorem contributingGroups_nodup {G : Garden w} (σ : Prescription G) : (contributingGroups G σ).Nodup := by
  unfold contributingGroups sgGroups
  exact ((Finset.nodup_toList _).filter _).filter _

/-- Actual contributing group lists correspond without any ordering assumption. -/
theorem BatchIso.contributingGroups_perm (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) :
    ((contributingGroups A.skeleton σ).map F.img).Perm
      (contributingGroups B.skeleton (transportPrescription F σ)) := by
  classical
  apply (List.perm_ext_iff_of_nodup ((contributingGroups_nodup σ).map F.img_injective)
    (contributingGroups_nodup (transportPrescription F σ))).mpr
  intro T
  constructor
  · intro hT
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
    obtain ⟨hm, hσ, ho⟩ := (mem_contributingGroups σ S).mp hS
    exact (mem_contributingGroups _ _).mpr ⟨F.maximalGroups_img hm,
      (transportPrescription_apply F σ S).trans hσ, (h.hasObj σ hA hm hσ).mpr ho⟩
  · intro hT
    obtain ⟨hm, hτ, ho⟩ := (mem_contributingGroups _ T).mp hT
    let S := F.symm.img T
    have hs : S ∈ maximalGroups A.skeleton.molecule := F.symm.maximalGroups_img hm
    have hσ : σ S = Molecule.GapKind.SG := hτ
    have he : F.img S = T := F.img_symm_img T
    have hso : HasObj A.skeleton S := (h.hasObj σ hA hs hσ).mp (by rw [he]; exact ho)
    exact List.mem_map.mpr ⟨S, (mem_contributingGroups σ S).mpr ⟨hs, hσ, hso⟩, he⟩

/-- B1b-2 (Mk-general form of `BatchIso.splice_repC`). -/
theorem BatchIso.splice_repCMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (z : GBranch A.skeleton.tree) :
    repC (stSt B.skeleton (transportPrescription F σ) Mk').cls (F.e z) =
      F.e (repC (stSt A.skeleton σ Mk).cls z) := by
  unfold repC
  rw [h.splice_classesMk σ hT hA z]
  cases (stSt A.skeleton σ Mk).cls z <;> rfl

/-- The actual representative map commutes with the actual batch atom map. -/
theorem BatchIso.splice_repC (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (z : GBranch A.skeleton.tree) :
    repC (stSt B.skeleton (transportPrescription F σ)).cls (F.e z) =
      F.e (repC (stSt A.skeleton σ).cls z) := h.splice_repCMk σ (Stage1Mk.markTransported_empty F) hA z

/-- B1b-2 (Mk-general form of `BatchIso.splice_pi`). -/
theorem BatchIso.splice_piMk (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    {Mk : Set (CLVine A.skeleton)} {Mk' : Set (CLVine B.skeleton)}
    (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk) (z : GBranch A.skeleton.tree) :
    (h.spliceMolIsoMk σ hT hA).e ((stSt A.skeleton σ Mk).M.pi (stSt A.skeleton σ Mk).hcls z) =
      (stSt B.skeleton (transportPrescription F σ) Mk').M.pi
        (stSt B.skeleton (transportPrescription F σ) Mk').hcls (F.e z) := by
  apply (stSt B.skeleton (transportPrescription F σ) Mk').M.ob_inj
  rw [h.spliceMolIso_branch_namesMk σ hT hA, SpMap.ob_pi, SpMap.ob_pi, h.splice_repCMk σ hT hA z]

/-- Actual group quotient images commute with the actual full batch splice map. -/
theorem BatchIso.splice_pi (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) (z : GBranch A.skeleton.tree) :
    (h.spliceMolIso σ hA).e ((stSt A.skeleton σ).M.pi (stSt A.skeleton σ).hcls z) =
      (stSt B.skeleton (transportPrescription F σ)).M.pi
        (stSt B.skeleton (transportPrescription F σ)).hcls (F.e z) :=
  h.splice_piMk σ (Stage1Mk.markTransported_empty F) hA z

/-- The entire actual collection support list is invariant through the actual splice map. -/
theorem BatchIso.objects_atoms_perm (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) :
    ((objects A.skeleton σ).map (fun O => (h.spliceMolIso σ hA).img O.atoms)).Perm
      ((objects B.skeleton (transportPrescription F σ)).map Object.atoms) := by
  have hp := (h.contributingGroups_perm σ hA).map
    (fun S => S.image ((stSt B.skeleton (transportPrescription F σ)).M.pi
      (stSt B.skeleton (transportPrescription F σ)).hcls))
  have he (S : Finset (GBranch A.skeleton.tree)) :
      (h.spliceMolIso σ hA).img (S.image ((stSt A.skeleton σ).M.pi (stSt A.skeleton σ).hcls)) =
        (F.img S).image ((stSt B.skeleton (transportPrescription F σ)).M.pi
          (stSt B.skeleton (transportPrescription F σ)).hcls) := by
    change (S.image _).image _ = (S.image _).image _
    rw [Finset.image_image, Finset.image_image]
    apply congrArg (fun f => S.image f)
    exact funext (h.splice_pi σ hA)
  have hs : ((objects A.skeleton σ).map (fun O => (h.spliceMolIso σ hA).img O.atoms)) =
      (contributingGroups A.skeleton σ).map (fun S =>
        (h.spliceMolIso σ hA).img (S.image ((stSt A.skeleton σ).M.pi (stSt A.skeleton σ).hcls))) := by
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (h.spliceMolIso σ hA).img) (objects_atoms_eq σ)
  rw [hs, objects_atoms_eq]
  simpa only [List.map_map, Function.comp_def, he] using hp

/-- The count of actual Cs collection choices is invariant, not an independently supplied count. -/
theorem BatchIso.collectionChoices_count (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton)
    (hA : IsV0Fam A.family σ) :
    (collectionChoices A.skeleton σ).count =
      (collectionChoices B.skeleton (transportPrescription F σ)).count := by
  have he := (h.objects_atoms_perm σ hA).length_eq
  change (objects A.skeleton σ).length = (objects B.skeleton (transportPrescription F σ)).length
  simpa only [List.length_map] using he

end WaveTurbulence.VineA
