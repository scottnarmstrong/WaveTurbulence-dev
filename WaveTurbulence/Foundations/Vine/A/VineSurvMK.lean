/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK3
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSurvMK4
public import WaveTurbulence.Foundations.FinalCount.AsmVN13
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: the survivor objects of `G_sb` (o75 Lemma 3, Theorem 7.5′(2))

`survObj ht` is B2a's image object of a survivor `t ∈ survivorsMk G σ Mk` (`survivorsMk_imageMK`), and
`survObjs G σ Mk` the list of them in the order of `survivorsMk` (group by group, along each spine).  Facts for the
world's `SurvivorData.Structural` (ruling R169):

* `survObj_objVine`: a survivor is a vine, or the HV of a one-survivor HVC (75-W1);
* `survObj_not_interior`: no hinge is interior to a survivor;
* `objects_disjoint_survObj`: survivors are disjoint from the objects of `𝒞₁` (which come from unmarked groups).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-- **The image of a survivor in `G_sb`** (B2a's `survivorsMk_imageMK`, in the form `survivorsMk_imageMK'` that
records the added bond of a 75-W1 HV). -/
noncomputable def survObj {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    Object (stSt G σ Mk).G.molecule :=
  Classical.choose (survivorsMk_imageMK' ht)

theorem survObj_spec' {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    (survObj ht).atoms = t.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
      (survObj ht).upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 ∧
      (survObj ht).lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) t.1 ∧
      (∀ c, (stSt G σ Mk).cls ((stSt G σ Mk).M.ob c) ≠ none → c ∈ (survObj ht).atoms →
        c = (survObj ht).upper ∨ c = (survObj ht).lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (stSt G σ Mk).cls z = none) ∧
      ((Vine.IsSomeVine (stSt G σ Mk).G.molecule (survObj ht).atoms (survObj ht).upper (survObj ht).lower ∧
          ∃ hvc, (survObj ht).shape = VineLikeObject.vc hvc) ∨
        (AllowedCollectionObject (stSt G σ Mk).G (survObj ht) ∧ ∃ R, (survObj ht).shape = VineLikeObject.hyper R ∧
          ¬ G.molecule.InGroup t.1 ((stSt G σ Mk).M.od R.added))) :=
  Classical.choose_spec (survivorsMk_imageMK' ht)

/-- The added bond of a 75-W1 survivor HV is not a bond of the survivor. -/
theorem survObj_hyper_added {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk)
    {R : HyperLikeRealization (stSt G σ Mk).G.molecule (survObj ht).atoms (survObj ht).upper (survObj ht).lower}
    (hR : (survObj ht).shape = VineLikeObject.hyper R) :
    ¬ G.molecule.InGroup t.1 ((stSt G σ Mk).M.od R.added) := by
  obtain ⟨-, -, -, -, -, -, h⟩ := survObj_spec' ht
  rcases h with ⟨-, hvc, hs⟩ | ⟨-, R', hs, hn⟩
  · rw [hR] at hs; cases hs
  · rw [hR] at hs
    cases hs
    exact hn

theorem survObj_spec {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    (survObj ht).atoms = t.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∧
      (survObj ht).upper = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.1 ∧
      (survObj ht).lower = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls t.2.2 ∧
      Set.InjOn ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) t.1 ∧
      (∀ c, (stSt G σ Mk).cls ((stSt G σ Mk).M.ob c) ≠ none → c ∈ (survObj ht).atoms →
        c = (survObj ht).upper ∨ c = (survObj ht).lower) ∧
      (∀ z ∈ t.1, z ≠ t.2.1 → z ≠ t.2.2 → (stSt G σ Mk).cls z = none) ∧
      ((Vine.IsSomeVine (stSt G σ Mk).G.molecule (survObj ht).atoms (survObj ht).upper (survObj ht).lower ∧
          ∃ hvc, (survObj ht).shape = VineLikeObject.vc hvc) ∨
        (AllowedCollectionObject (stSt G σ Mk).G (survObj ht) ∧ ∃ R, (survObj ht).shape = VineLikeObject.hyper R)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := survObj_spec' ht
  exact ⟨h1, h2, h3, h4, h5, h6, h7.imp id fun hh => ⟨hh.1, hh.2.imp fun _ hR => hR.1⟩⟩

/-- The survivor objects of `G_sb`, in the order of `survivorsMk`. -/
noncomputable def survObjs (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G)) :
    List (Object (stSt G σ Mk).G.molecule) :=
  (survivorsMk G σ Mk).attach.map fun t => survObj t.2

theorem survObjs_length (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G)) :
    (survObjs G σ Mk).length = (survivorsMk G σ Mk).length := by
  simp [survObjs]

/-- **A survivor is a vine, or the HV of a one-survivor HVC** (o75 Theorem 7.5′(2), 75-W1; R169). -/
theorem survObj_objVine {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    FinalCountAsm.ObjVine (stSt G σ Mk).G.molecule (survObj ht) := by
  obtain ⟨-, -, -, -, -, -, h⟩ := survObj_spec ht
  unfold FinalCountAsm.ObjVine
  rcases h with ⟨⟨X, hX⟩, hvc, hs⟩ | ⟨hA, R, hs⟩
  · rw [hs]; exact ⟨X, hX⟩
  · rw [hs]
    unfold AllowedCollectionObject at hA
    rw [hs] at hA
    obtain ⟨X, hX⟩ := hA
    exact ⟨X, hX⟩

/-- **No hinge is interior to a survivor.** -/
theorem survObj_not_interior {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk)
    {v : GBranch (stSt G σ Mk).G.tree} (hv : v ∈ (stSt G σ Mk).hinges) : ¬ (survObj ht).IsInterior v := by
  rintro ⟨hva, hu, hl⟩
  obtain ⟨-, -, -, -, hj, -⟩ := survObj_spec ht
  rcases hj v (((stSt G σ Mk).mem_hinges v).mp hv) hva with h | h
  · exact hu h
  · exact hl h

/-- The group of a survivor. -/
theorem survivorsMk_group {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    ∃ S, S ∈ maximalGroups G.molecule ∧ σ S = Molecule.GapKind.SG ∧ ∃ h : markedGroup G Mk S,
      t ∈ (markedUnitsOfMK h).surv ∧ t.1 ⊆ S :=
  by
  obtain ⟨S, hS, hσ, h, htm⟩ := mem_survivorsMk_iffMK.mp ht
  obtain ⟨-, hI, -⟩ := (markedUnitsOfMK h).surv_spec t htm
  exact ⟨S, hS, hσ, h, htm, isIngredient_subset hI⟩

/-- An object of `𝒞₁` comes from an unmarked group. -/
theorem objOf_not_marked {σ : Prescription G} {S : Finset (GBranch G.tree)} {Mk : Set (CLVine G)}
    {O : Object (stSt G σ Mk).G.molecule} (h : O ∈ objOf G σ S Mk) : ¬ markedGroup G Mk S := by
  classical
  unfold objOf at h
  split_ifs at h with hex
  · exact hex.2.2.2.2.1
  · cases h

theorem mem_objects_group {σ : Prescription G} {Mk : Set (CLVine G)} {O : Object (stSt G σ Mk).G.molecule}
    (h : O ∈ objects G σ Mk) : ∃ S, S ∈ maximalGroups G.molecule ∧ ¬ markedGroup G Mk S ∧
      ∀ v ∈ O.atoms, ∃ z ∈ S, v = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z := by
  unfold objects at h
  obtain ⟨S, -, hS⟩ := List.mem_filterMap.mp h
  obtain ⟨-, hSm, -, hspec⟩ := objOf_specMk (Mk := Mk) (Option.mem_def.mpr hS)
  exact ⟨S, hSm, objOf_not_marked (Option.mem_def.mpr hS), hspec.atoms_sub⟩

/-- **Survivors are disjoint from the objects of `𝒞₁`** (o75 Theorem 7.5′(2)). -/
theorem objects_disjoint_survObj (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
    {O : Object (stSt G σ Mk).G.molecule} (hO : O ∈ objects G σ Mk)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    Disjoint O.atoms (survObj ht).atoms := by
  obtain ⟨S', hS', hnm, hsub⟩ := mem_objects_group hO
  obtain ⟨S, hS, -, hmk, -, htS⟩ := survivorsMk_group ht
  obtain ⟨hat, -⟩ := survObj_spec ht
  rw [Finset.disjoint_left]
  intro v hvO hvt
  rw [hat] at hvt
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hvt
  obtain ⟨z', hz', he⟩ := hsub _ hvO
  have hSS := group_eq_of_pi_eq hM σ hS hS' (htS hz) hz' he
  subst hSS
  exact hnm hmk

end WaveTurbulence.VineA.NormalizedSplice
