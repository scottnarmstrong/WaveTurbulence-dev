/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Geometry.SubproMeetBMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproItemsMK
public import WaveTurbulence.Foundations.Stage1.Geometry.SubproSupportAR83
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: the main-side producer of `SubproSupportMK` (o75 Theorem 7.5′ (2), (4)–(6′))

`SubproSupportMKAt G C surv …` is the world's `FinalMKDefs.SubproSupportMK G C S …` (C0 SCOPE §4.1) written for a
family of survivor objects `surv : Fin m → Object G.molecule`, with `S.joints` spelled out as `survJointsOf surv` and
`SurvFirstJoint` unfolded; for `S := ⟨m, surv, prot⟩` the two agree field by field (the world's definitions unfold to
these).  `subproSupportMKAt` proves it for the marked splice `stSt G σ Mk`, with `C := collectionChoices G σ Mk` and
`surv := (survObjs G σ Mk).get`, on one decoration of the support, under ruling R173 (`hMkSG : Mk ⊆ vinesV0 G σ`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineA.NormalizedSplice.Subpro
open WaveTurbulence.Subpro WaveTurbulence.VineA.NormalizedSplice
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice
  WaveTurbulence.Stage1

/-- The exceptional joints `B` of a family of survivor objects (the world's `SurvivorData.joints`). -/
noncomputable def survJointsOf {w : ℕ} {G : Garden w} {m : ℕ} (surv : Fin m → Object G.molecule) :
    Finset (GBranch G.tree) :=
  Finset.univ.biUnion fun i => {(surv i).upper, (surv i).lower}

theorem mem_survJointsOf {w : ℕ} {G : Garden w} {m : ℕ} {surv : Fin m → Object G.molecule}
    {v : GBranch G.tree} : v ∈ survJointsOf surv ↔ ∃ i, v = (surv i).upper ∨ v = (surv i).lower := by
  simp [survJointsOf]

/-- The world's `SubproSupportMK` (Theorem 7.5′ (4), (5) incl. 75-F1, (6), (6′)) for the survivors `surv`. -/
structure SubproSupportMKAt {w d : ℕ} (G : Garden w) (C : SubproChoices G) {m : ℕ}
    (surv : Fin m → Object G.molecule) (L γ η : ℝ)
    (base : Mom d) (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ)) : Prop where
  selectedSG : ∀ i, (C.collection i).HasGapKind L γ η base κ .SG
  survivorSG : ∀ i, (surv i).HasGapKind L γ η base κ .SG
  zeroTame : ∀ v, v ∉ C.hinges →
    (∃ x y, TripleAt G v x y ∧ Molecule.gapAt L base κ x y = 0) → G.molecule.IsTame L base kFix κ v
  contained : ∀ P : Object G.molecule,
    P.HasGapKind L γ η base κ .SG → C.OutsideAtoms P → (∀ i, ¬ P.atoms ⊆ (surv i).atoms) →
      Disjoint P.atoms (C.hinges ∪ survJointsOf surv) →
    (∃ S' a b, IsDV G.molecule S' a b ∧ P.atoms ⊆ S' ∧ Disjoint S' (C.hinges ∪ survJointsOf surv) ∧
      (∀ i, Disjoint S' (C.collection i).atoms) ∧ ∀ i, Disjoint S' (surv i).atoms) ∨
    ∃ Q : Object G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η base κ .LG ∨ Q.HasGapKind L γ η base κ .ZG) ∧
      Disjoint Q.atoms (C.hinges ∪ survJointsOf surv) ∧ (∀ i, Disjoint Q.atoms (C.collection i).atoms) ∧
      ∀ i, Disjoint Q.atoms (surv i).atoms
  hingeSG : ∀ v ∈ C.hinges, HasChosenPair (C.first v) (C.second v) (fun x y =>
    TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG)
  hingeJoint : ∀ v ∈ C.hinges, ∀ i,
    (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
      HasChosenPair (C.first v) (C.second v) (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)
  jointPair : ∀ i v, ((v = (surv i).upper ∨ v = (surv i).lower) ∧
      ∀ j, j < i → ¬ (v = (surv j).upper ∨ v = (surv j).lower)) →
      HasChosenPair (C.first v) (C.second v) (fun x y => (surv i).ContainsDart x ∧ (surv i).ContainsDart y)
  crossing : ∀ P : Object G.molecule,
    P.HasGapKind L γ η base κ .SG → C.OutsideAtoms P → (∀ i, ¬ P.atoms ⊆ (surv i).atoms) →
      Disjoint P.atoms (survJointsOf surv) → ¬ Disjoint P.atoms C.hinges →
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧
      ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))
  meetB : ∀ P : Object G.molecule, P.HasGapKind L γ η base κ .SG → ¬ Disjoint P.atoms (survJointsOf surv) →
    (∃ i, P.atoms ⊆ (surv i).atoms) ∨ (∃ i x, P.ContainsDart x ∧ (surv i).ContainsDart x) ∨
    ∃ v ∈ C.hinges, v ∈ P.atoms ∧ ((v ≠ P.upper ∧ v ≠ P.lower) ∨
        ((v = P.upper ∨ v = P.lower) ∧
          HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y))))

variable {R : ℕ} {G : Garden (2 * R)}

/-- Every survivor object is listed in `survObjs`. -/
theorem survObj_mem_get {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ survivorsMk G σ Mk) :
    ∃ i, (survObjs G σ Mk).get i = survObj ht := by
  have hmem : survObj ht ∈ survObjs G σ Mk := by
    unfold survObjs
    exact List.mem_map.mpr ⟨⟨t, ht⟩, List.mem_attach _ _, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  exact ⟨i, hi⟩

/-- Disjointness from the survivors gives disjointness from their joints. -/
theorem disjoint_survJointsOf {w : ℕ} {G' : Garden w} {m : ℕ} {surv : Fin m → Object G'.molecule}
    {X : Finset (GBranch G'.tree)} (h : ∀ i, Disjoint X (surv i).atoms) : Disjoint X (survJointsOf surv) := by
  rw [Finset.disjoint_left]
  intro v hvX hv
  obtain ⟨i, hi⟩ := mem_survJointsOf.mp hv
  rcases hi with rfl | rfl
  · exact Finset.disjoint_left.mp (h i) hvX (Object.upper_mem _)
  · exact Finset.disjoint_left.mp (h i) hvX (Object.lower_mem _)

/-- **The main-side `SubproSupportMK`** (o75 Theorem 7.5′ (2), (4), (5) with 75-F1, (6), (6′)) for the marked
splice, `C := collectionChoices G σ Mk` and the survivors `(survObjs G σ Mk).get`, on one decoration of the support.
Ruling R173: `hMkSG : Mk ⊆ vinesV0 G σ`. -/
theorem subproSupportMKAt (σ : Prescription G) {Mk : Set (CLVine G)} (hMkSG : Mk ⊆ vinesV0 G σ) {d : ℕ}
    (D : SplicedKernelData (stSt G σ Mk).G d) (hD : D.gapSpecification = gapSpecificationMk G σ Mk)
    (hpl : (stSt G σ Mk).G.IsPlain) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (z : GenDecoration (stSt G σ Mk).G d roots 0)
    (hε : splicedEpsilon (stSt G σ Mk).G (collectionChoices G σ Mk).hinges z.1 ≠ 0)
    (hZ : splicedGapIndicator (stSt G σ Mk).G D L γ η base z.1 ≠ 0) :
    SubproSupportMKAt (stSt G σ Mk).G (collectionChoices G σ Mk) (survObjs G σ Mk).get L γ η base
      (Finset.univ.image (fun i => base + latticePoint L (roots i))) (bondIndex (stSt G σ Mk).G z.1) := by
  classical
  have hdec := sbDec_of_genMk σ hpl hL base roots z
  have hM : G.molecule.IsMolecule := WaveTurbulence.Mole.garden_isMolecule G
  -- conversions between the indexed survivors and `survObj`
  have hout' : ∀ P : Object (stSt G σ Mk).G.molecule, (collectionChoices G σ Mk).OutsideAtoms P →
      ∀ O ∈ objects G σ Mk, ¬ P.atoms ⊆ O.atoms := by
    intro P hout O hO
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hO
    have := hout i
    simp only [collectionChoices] at this
    rw [hi] at this
    exact this
  have hsurv' : ∀ P : Object (stSt G σ Mk).G.molecule,
      (∀ i, ¬ P.atoms ⊆ ((survObjs G σ Mk).get i).atoms) →
      ∀ t (ht : t ∈ survivorsMk G σ Mk), ¬ P.atoms ⊆ (survObj ht).atoms := by
    intro P h t ht
    obtain ⟨i, hi⟩ := survObj_mem_get ht
    rw [← hi]
    exact h i
  have hJ' : ∀ P : Object (stSt G σ Mk).G.molecule,
      Disjoint P.atoms (survJointsOf (survObjs G σ Mk).get) →
      ∀ t (ht : t ∈ survivorsMk G σ Mk), (survObj ht).upper ∉ P.atoms ∧ (survObj ht).lower ∉ P.atoms := by
    intro P h t ht
    obtain ⟨i, hi⟩ := survObj_mem_get ht
    refine ⟨fun hu => Finset.disjoint_left.mp h hu (mem_survJointsOf.mpr ⟨i, Or.inl (by rw [hi])⟩),
      fun hl => Finset.disjoint_left.mp h hl (mem_survJointsOf.mpr ⟨i, Or.inr (by rw [hi])⟩)⟩
  have hsd : ∀ X : Finset (GBranch (stSt G σ Mk).G.tree),
      (∀ t (ht : t ∈ survivorsMk G σ Mk), Disjoint X (survObj ht).atoms) →
      ∀ i, Disjoint X ((survObjs G σ Mk).get i).atoms := by
    intro X h i
    obtain ⟨j, hj, -, hgi⟩ := survObjs_get i
    rw [hgi]
    exact h _ hj
  have hobj : ∀ X : Finset (GBranch (stSt G σ Mk).G.tree), (∀ O ∈ objects G σ Mk, Disjoint X O.atoms) →
      ∀ i, Disjoint X ((collectionChoices G σ Mk).collection i).atoms := fun X h i => h _ (List.get_mem _ _)
  refine ⟨selectedSG_cc2Mk σ D hD L γ η base z.1 hZ hdec, ?_, zeroTame_cc2Mk σ hpl hL base roots z hε, ?_,
    hingeSG_cc2Mk σ D hD L γ η base z.1 hZ hdec, hingeJoint_cc2Mk σ, ?_, ?_, ?_⟩
  · -- survivorSG
    intro i
    obtain ⟨j, hj, -, hgi⟩ := survObjs_get i
    rw [hgi]
    exact survObj_SG hM σ L γ η base z.1 D hD hZ hdec.c hj
  · -- contained (4)
    intro P _ hout hsv hdis
    have hdisH : Disjoint P.atoms (stSt G σ Mk).hinges :=
      Finset.disjoint_of_subset_right Finset.subset_union_left hdis
    have hdisB : Disjoint P.atoms (survJointsOf (survObjs G σ Mk).get) :=
      Finset.disjoint_of_subset_right Finset.subset_union_right hdis
    rcases contained_atomsMk hM σ hMkSG D hD L γ η base z.1 hZ P (hout' P hout) (hsurv' P hsv) hdisH
        (hJ' P hdisB) with ⟨S', a, b, h1, h2, h3, h4, h5⟩ | ⟨Q, h1, h2, h3, h4, h5⟩
    · exact Or.inl ⟨S', a, b, h1, h2,
        Finset.disjoint_union_right.mpr ⟨h3, disjoint_survJointsOf (hsd S' h5)⟩, hobj S' h4, hsd S' h5⟩
    · exact Or.inr ⟨Q, h1, h2,
        Finset.disjoint_union_right.mpr ⟨h3, disjoint_survJointsOf (hsd Q.atoms h5)⟩, hobj Q.atoms h4,
        hsd Q.atoms h5⟩
  · -- jointPair (75-F1)
    intro i v h
    exact jointPair_survObjs hM σ i v h.1 h.2
  · -- crossing (6)
    intro P _ hout _ hdisB hnd
    exact crossing_atomsMk hM σ P (hout' P hout) (hJ' P hdisB) hnd
  · -- meetB (6′)
    intro P _ hmeet
    have hm : ∃ t, ∃ ht : t ∈ survivorsMk G σ Mk, (survObj ht).upper ∈ P.atoms ∨ (survObj ht).lower ∈ P.atoms := by
      obtain ⟨v, hvP, hvB⟩ := Finset.not_disjoint_iff.mp hmeet
      obtain ⟨i, hi⟩ := mem_survJointsOf.mp hvB
      obtain ⟨j, hj, -, hgi⟩ := survObjs_get i
      rw [hgi] at hi
      rcases hi with rfl | rfl
      · exact ⟨_, hj, Or.inl hvP⟩
      · exact ⟨_, hj, Or.inr hvP⟩
    rcases meetB_atomsMk hM σ P hm with ⟨t, ht, h⟩ | ⟨t, ht, x, hx1, hx2⟩ | h
    · obtain ⟨i, hi⟩ := survObj_mem_get ht
      exact Or.inl ⟨i, hi ▸ h⟩
    · obtain ⟨i, hi⟩ := survObj_mem_get ht
      exact Or.inr (Or.inl ⟨i, x, hx1, hi ▸ hx2⟩)
    · exact Or.inr (Or.inr h)

end WaveTurbulence.VineA.NormalizedSplice.Subpro
