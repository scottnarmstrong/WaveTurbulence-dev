/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKGarden.PoolF
public import WaveTurbulence.Foundations.FinalCount.AsmGTrans

/-! # C1c MK-GARDEN / ObligMK: the survivor-aware obligations, garden to `inlMol`

* `subproOblGMK_of_supportMK`: the garden's `SubproSupportMK` is `SubproOblGMK` of `collDataOf C` with the survivors
  `S.surv` (field for field, as main's `subproOblG_of_support`);
* `subproOblGMK_base_indep`: the obligations do not depend on the base momentum (as main's `subproOblG_base_indep`);
* `collMap_subproOblGMK`: they transport along an atom renaming (forward half of main's `collMap_subproOblG`), with
  the survivors through `objMap`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical

namespace WaveTurbulence.Flower.FinalMKGarden
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
  WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.AtomTransport WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.MkDefs

section base
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem hostE_base {M : Molecule V D} {C : CollData M} {m : ℕ} {E : Fin m → Object M} {L γ η : ℝ} {w w' : Mom d}
    {κ : D → (Fin d → ℤ)} {P : Object M} (h : HostE C E L γ η w κ P) : HostE C E L γ η w' κ P := by
  rcases h with ⟨S, a, b, h1, h2, h3, h4, h5⟩ | ⟨Q, h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨S, a, b, h1, h2, h3, h4, h5⟩
  · refine Or.inr ⟨Q, h1, ?_, h3, h4, h5⟩
    rcases h2 with h2 | h2
    · exact Or.inl ((object_hasGapKind_base_indep Q L γ η w w' κ _).1 h2)
    · exact Or.inr ((object_hasGapKind_base_indep Q L γ η w w' κ _).1 h2)

/-- The survivor-aware obligations do not depend on the base momentum. -/
theorem subproOblGMK_base_indep {M : Molecule V D} {C : CollData M} {m : ℕ} {E : Fin m → Object M} {L γ η : ℝ}
    {w w' : Mom d} {κ : D → (Fin d → ℤ)} (h : SubproOblGMK C E L γ η w κ) : SubproOblGMK C E L γ η w' κ := by
  have hsg : ∀ P : Object M, P.HasGapKind L γ η w' κ .SG → P.HasGapKind L γ η w κ .SG :=
    fun P => (object_hasGapKind_base_indep P L γ η w w' κ _).2
  refine ⟨fun i => (object_hasGapKind_base_indep _ L γ η w w' κ _).1 (h.survSG i),
    fun P hP hO hn hD => hostE_base (h.contained P (hsg P hP) hO hn hD), fun v hv => ?_, h.hingeJoint, h.jointPair,
    fun P hP hO hn hD hH => h.crossing P (hsg P hP) hO hn hD hH, fun P hP hB => h.meetB P (hsg P hP) hB⟩
  exact (hasChosenPair_congr' fun x y => by simp only [gapAt_base_indep L w w' κ]).1 (h.hingeSG v hv)

end base

section map
variable {V W : Type*} [DecidableEq V] [DecidableEq W] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
  {M₀ : Molecule V D} (ι : V ↪ W) {m : ℕ}

theorem survJointsM_objMap (E : Fin m → Object M₀) :
    survJointsM (fun i => objMap (ι := ι) (E i)) = (survJointsM E).map ι := by
  ext v
  simp only [survJointsM, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_map, objMap_upper, objMap_lower]
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact ⟨_, ⟨i, Or.inl rfl⟩, rfl⟩
    · exact ⟨_, ⟨i, Or.inr rfl⟩, rfl⟩
  · rintro ⟨a, ⟨i, rfl | rfl⟩, rfl⟩
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr rfl⟩

theorem survAtomsM_objMap (E : Fin m → Object M₀) :
    survAtomsM (fun i => objMap (ι := ι) (E i)) = (survAtomsM E).map ι := by
  ext v
  simp only [survAtomsM, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_map, objMap_atoms]
  constructor
  · rintro ⟨i, a, ha, rfl⟩
    exact ⟨a, ⟨i, ha⟩, rfl⟩
  · rintro ⟨a, ⟨i, ha⟩, rfl⟩
    exact ⟨i, a, ha, rfl⟩

/-- The hinge alternative of `crossing`/`meetB` along an atom renaming. -/
theorem hingeCase_map (C : CollData M₀) (P : Object M₀) {v : V}
    (hrest : (v ≠ P.upper ∧ v ≠ P.lower) ∨ ((v = P.upper ∨ v = P.lower) ∧
      HasChosenPair (C.first v) (C.second v) (fun x y => Xor (P.ContainsDart x) (P.ContainsDart y)))) :
    (ι v ≠ (objMap (ι := ι) P).upper ∧ ι v ≠ (objMap (ι := ι) P).lower) ∨
      ((ι v = (objMap (ι := ι) P).upper ∨ ι v = (objMap (ι := ι) P).lower) ∧
      HasChosenPair ((collMap ι C).first (ι v)) ((collMap ι C).second (ι v))
        (fun x y => Xor ((objMap (ι := ι) P).ContainsDart x) ((objMap (ι := ι) P).ContainsDart y))) := by
  rcases hrest with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by simpa [ι.injective.eq_iff] using h1, by simpa [ι.injective.eq_iff] using h2⟩
  · refine Or.inr ⟨by simpa [ι.injective.eq_iff] using h1, ?_⟩
    rw [hasChosenPair_map]
    exact (hasChosenPair_congr fun x y => by rw [objMap_containsDart_iff, objMap_containsDart_iff]).mpr h2

theorem disjoint_map_union {S H J : Finset V} : Disjoint (S.map ι) (H.map ι ∪ J.map ι) ↔ Disjoint S (H ∪ J) := by
  rw [← Finset.map_union, Finset.disjoint_map]

/-- **Atom renaming of the survivor-aware obligations** (forward half of main's `collMap_subproOblG`). -/
theorem collMap_subproOblGMK (C : CollData M₀) (E : Fin m → Object M₀) {L γ η : ℝ} {w : Mom d}
    {κ : D → (Fin d → ℤ)} (h : SubproOblGMK C E L γ η w κ) :
    SubproOblGMK (collMap ι C) (fun i => objMap (ι := ι) (E i)) L γ η w κ := by
  have hsub : ∀ A B : Finset V, A.map ι ⊆ B.map ι ↔ A ⊆ B := fun A B => Finset.map_subset_map
  refine ⟨fun i => (objMap_hasGapKind_iff (E i) L γ η w κ _).mpr (h.survSG i), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P' hP hO hn hD
    obtain ⟨P, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) P'
    have hD0 : Disjoint P.atoms (C.hinges ∪ survJointsM E) := by
      have := hD
      rw [collMap_hinges, survJointsM_objMap, objMap_atoms, disjoint_map_union] at this
      exact this
    rcases h.contained P ((objMap_hasGapKind_iff P L γ η w κ _).mp hP) ((collMap_outside ι C P).mp hO)
        (fun i hs => hn i ((hsub _ _).2 hs)) hD0 with
      ⟨S, a, b, hdv, hs, hd1, hd2, hd3⟩ | ⟨Q, hs, hk, hd1, hd2, hd3⟩
    · refine Or.inl ⟨S.map ι, ι a, ι b, (mapAtoms_isDV M₀ ι S a b).mpr hdv, (hsub _ _).2 hs, ?_,
        fun i => (Finset.disjoint_map ι).mpr (hd2 i), fun i => (Finset.disjoint_map ι).mpr (hd3 i)⟩
      rw [collMap_hinges, survJointsM_objMap, disjoint_map_union]
      exact hd1
    · refine Or.inr ⟨objMap Q, (hsub _ _).2 hs, ?_, ?_, fun i => (Finset.disjoint_map ι).mpr (hd2 i),
        fun i => (Finset.disjoint_map ι).mpr (hd3 i)⟩
      · rcases hk with hk | hk
        · exact Or.inl ((objMap_hasGapKind_iff Q L γ η w κ _).mpr hk)
        · exact Or.inr ((objMap_hasGapKind_iff Q L γ η w κ _).mpr hk)
      · rw [collMap_hinges, survJointsM_objMap, objMap_atoms, disjoint_map_union]
        exact hd1
  · intro v' hv'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (by simpa using hv')
    rw [hasChosenPair_map]
    exact (hasChosenPair_congr fun x y => by rw [tripleAtM_iff]).mpr (h.hingeSG v hv)
  · intro v' hv' (i : Fin C.n) hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (by simpa using hv')
    rw [hasChosenPair_map]
    exact (hasChosenPair_congr fun x y => by
      rw [collMap_collection, objMap_containsDart_iff, objMap_containsDart_iff]).mpr
      (h.hingeJoint v hv i (by simpa [collMap_collection, objMap_upper, objMap_lower, ι.injective.eq_iff] using hi))
  · intro i v' hv'
    have hj : v' = ι (E i).upper ∨ v' = ι (E i).lower := hv'.1
    obtain ⟨v, rfl⟩ : ∃ v, v' = ι v := by
      rcases hj with e | e
      · exact ⟨_, e⟩
      · exact ⟨_, e⟩
    have hv : SurvFirstJointM E i v := by
      refine ⟨?_, fun j hjl hjv => hv'.2 j hjl ?_⟩
      · rcases hj with e | e
        · exact Or.inl (ι.injective e)
        · exact Or.inr (ι.injective e)
      · rcases hjv with e | e
        · exact Or.inl (show ι v = ι (E j).upper by rw [e])
        · exact Or.inr (show ι v = ι (E j).lower by rw [e])
    rw [hasChosenPair_map]
    exact (hasChosenPair_congr fun x y => by rw [objMap_containsDart_iff, objMap_containsDart_iff]).mpr
      (h.jointPair i v hv)
  · intro P' hP hO hn hJ hH
    obtain ⟨P, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) P'
    have hJ0 : Disjoint P.atoms (survJointsM E) := by
      have := hJ
      rw [survJointsM_objMap, objMap_atoms, Finset.disjoint_map] at this
      exact this
    obtain ⟨v, hv, hvP, hrest⟩ := h.crossing P ((objMap_hasGapKind_iff P L γ η w κ _).mp hP)
      ((collMap_outside ι C P).mp hO) (fun i hs => hn i ((hsub _ _).2 hs)) hJ0
      (fun hd => hH ((collMap_disjoint_hinges ι C P).mpr hd))
    exact ⟨ι v, by simpa using hv, by simpa using hvP, hingeCase_map ι C P hrest⟩
  · intro P' hP hB
    obtain ⟨P, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) P'
    have hB0 : ¬ Disjoint P.atoms (survJointsM E) := by
      intro hd
      apply hB
      rw [survJointsM_objMap, objMap_atoms, Finset.disjoint_map]
      exact hd
    rcases h.meetB P ((objMap_hasGapKind_iff P L γ η w κ _).mp hP) hB0 with ⟨i, hi⟩ | ⟨i, x, hx1, hx2⟩ |
      ⟨v, hv, hvP, hrest⟩
    · exact Or.inl ⟨i, (hsub _ _).2 hi⟩
    · exact Or.inr (Or.inl ⟨i, x, (objMap_containsDart_iff P x).mpr hx1, (objMap_containsDart_iff (E i) x).mpr hx2⟩)
    · exact Or.inr (Or.inr ⟨ι v, by simpa using hv, by simpa using hvP, hingeCase_map ι C P hrest⟩)

end map

section garden
variable {w d : ℕ} {G : Garden w}

/-- **The garden's survivor-aware support is the survivor-aware obligation** (field for field). -/
theorem subproOblGMK_of_supportMK {C : SubproChoices G} {S : SurvivorData G} {L γ η : ℝ} {base : Mom d}
    {kFix : Finset (Mom d)} {κ : GardenDart G → (Fin d → ℤ)} (h : SubproSupportMK G C S L γ η base kFix κ) :
    SubproOblGMK (Subpro.collDataOf C) S.surv L γ η base κ :=
  ⟨h.survivorSG, h.contained, h.hingeSG, h.hingeJoint, h.jointPair, h.crossing, h.meetB⟩

end garden

end WaveTurbulence.Flower.FinalMKGarden
