/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AtMapSubpro
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AtMapObject
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunE
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCSource
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AtMapSubpro`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # ATOM-TRANSPORT, part 5: the collection data and the named obligations of `subpro`

`collMap ι C` is the collection data (`C₁`, hinges, designated pairs) of `mapAtoms M₀ ι` obtained from those of
`M₀`.  `SubproOblG`, `UnselOK` (with `C2Of`), `DegenSGT`, `SGat`, `IsTame`, `SourceLadderGaps` hold for the
transported data iff they hold for the original (both directions; every object of `mapAtoms M₀ ι` is an
`objMap`, so every unselected set of `mapAtoms M₀ ι` is the image of one of `M₀`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.AtomTransport
open WaveTurbulence WaveTurbulence.MoleProp WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCountG3
  WaveTurbulence.VineCount

universe u
variable {V W : Type*} [DecidableEq V] [DecidableEq W] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀} (ι : V ↪ W)

/-- The collection data of `M₀` as collection data of `mapAtoms M₀ ι`: the objects through `objMap`, the hinges
through `ι`, the designated bonds extended by `none` off the image. -/
noncomputable def collMap (C : CollData M₀) : CollData (mapAtoms M₀ ι) where
  n := C.n
  collection := fun i => objMap (C.collection i)
  hinges := C.hinges.map ι
  first := Function.extend ι C.first (fun _ => none)
  second := Function.extend ι C.second (fun _ => none)

@[simp] theorem collMap_first (C : CollData M₀) (v : V) : (collMap ι C).first (ι v) = C.first v :=
  ι.injective.extend_apply C.first (fun _ => none) v
@[simp] theorem collMap_second (C : CollData M₀) (v : V) : (collMap ι C).second (ι v) = C.second v :=
  ι.injective.extend_apply C.second (fun _ => none) v
@[simp] theorem collMap_hinges (C : CollData M₀) : (collMap ι C).hinges = C.hinges.map ι := rfl
@[simp] theorem collMap_collection (C : CollData M₀) (i : Fin C.n) :
    (collMap ι C).collection i = objMap (C.collection i) := rfl

theorem hasChosenPair_map (C : CollData M₀) (v : V) (P : D₀ → D₀ → Prop) :
    HasChosenPair ((collMap ι C).first (ι v)) ((collMap ι C).second (ι v)) P ↔
      HasChosenPair (C.first v) (C.second v) P := by
  rw [collMap_first, collMap_second]

theorem collMap_outside (C : CollData M₀) (P : Src.Object Src.γL M₀) :
    (collMap ι C).Outside (objMap P) ↔ C.Outside P := by
  unfold CollData.Outside
  exact forall_congr' fun i => not_congr Finset.map_subset_map

theorem collMap_disjoint_hinges (C : CollData M₀) (P : Src.Object Src.γL M₀) :
    Disjoint (objMap (ι := ι) P).atoms (collMap ι C).hinges ↔ Disjoint P.atoms C.hinges := by
  simp [Finset.disjoint_map]

theorem collMap_host (C : CollData M₀) (P : Src.Object Src.γL M₀) :
    (collMap ι C).Host L γ η w κ (objMap P) ↔ C.Host L γ η w κ P := by
  unfold CollData.Host
  constructor
  · rintro (⟨S', a', b', hdv, hsub, hdis, hdis2⟩ | ⟨Q', hsub, hk, hdis, hdis2⟩)
    · obtain ⟨S, a, b, rfl, rfl, rfl, hdv2⟩ := exists_isDV_of_mapAtoms M₀ ι hdv
      refine Or.inl ⟨S, a, b, hdv2, ?_, ?_, fun i => ?_⟩
      · simpa [Finset.map_subset_map] using hsub
      · simpa [Finset.disjoint_map] using hdis
      · exact (Finset.disjoint_map ι).mp (hdis2 i)
    · obtain ⟨Q, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) Q'
      refine Or.inr ⟨Q, ?_, ?_, ?_, fun i => ?_⟩
      · simpa [Finset.map_subset_map] using hsub
      · rcases hk with hk | hk
        · exact Or.inl ((objMap_hasGapKind_iff Q L γ η w κ _).mp hk)
        · exact Or.inr ((objMap_hasGapKind_iff Q L γ η w κ _).mp hk)
      · simpa [Finset.disjoint_map] using hdis
      · exact (Finset.disjoint_map ι).mp (hdis2 i)
  · rintro (⟨S, a, b, hdv, hsub, hdis, hdis2⟩ | ⟨Q, hsub, hk, hdis, hdis2⟩)
    · refine Or.inl ⟨S.map ι, ι a, ι b, (mapAtoms_isDV M₀ ι S a b).mpr hdv, ?_, ?_, fun i => ?_⟩
      · simpa [Finset.map_subset_map] using hsub
      · simpa [Finset.disjoint_map] using hdis
      · exact (Finset.disjoint_map ι).mpr (hdis2 i)
    · refine Or.inr ⟨objMap Q, ?_, ?_, ?_, fun i => ?_⟩
      · simpa [Finset.map_subset_map] using hsub
      · rcases hk with hk | hk
        · exact Or.inl ((objMap_hasGapKind_iff Q L γ η w κ _).mpr hk)
        · exact Or.inr ((objMap_hasGapKind_iff Q L γ η w κ _).mpr hk)
      · simpa [Finset.disjoint_map] using hdis
      · exact (Finset.disjoint_map ι).mpr (hdis2 i)

theorem collMap_inP (C : CollData M₀) (P : Src.Object Src.γL M₀) :
    (collMap ι C).InP L γ η w κ (objMap P) ↔ C.InP L γ η w κ P := by
  unfold CollData.InP
  rw [objMap_hasGapKind_iff, collMap_outside, collMap_disjoint_hinges, collMap_host]

theorem mem_collMap_c2Of (C : CollData M₀) (Unsel : Set (Src.Object Src.γL M₀)) (U : Src.Object Src.γL M₀) :
    objMap (ι := ι) U ∈ (collMap ι C).C2Of L γ η w κ (objMap '' Unsel) ↔ U ∈ C.C2Of L γ η w κ Unsel := by
  have hun : ∀ Q : Src.Object Src.γL M₀, objMap (ι := ι) Q ∈ objMap '' Unsel ↔ Q ∈ Unsel := fun Q =>
    ⟨fun ⟨Q2, h, e⟩ => objMap_injective e ▸ h, fun h => ⟨Q, h, rfl⟩⟩
  unfold CollData.C2Of
  simp only [Set.mem_ofPred_eq, collMap_inP, hun]
  refine and_congr Iff.rfl ⟨fun h Q hQ hUQ => ?_, fun h Q' hQ' hUQ => ?_⟩
  · have := h (objMap Q) (by rwa [collMap_inP, hun]) (by simpa [Finset.map_subset_map] using hUQ)
    simpa [Finset.map_subset_map] using this
  · obtain ⟨Q, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) Q'
    rw [collMap_inP, hun] at hQ'
    have := h Q hQ' (by simpa [Finset.map_subset_map] using hUQ)
    simpa [Finset.map_subset_map] using this

theorem objMap_hyper_iff (U : Src.Object Src.γL M₀) :
    (∃ R, (objMap (ι := ι) U).shape = Src.VineLikeObject.hyper R) ↔ ∃ R, U.shape = Src.VineLikeObject.hyper R := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc h => exact ⟨fun ⟨R, h'⟩ => (by cases h'), fun ⟨R, h'⟩ => (by cases h')⟩
  | hyper R => exact ⟨fun _ => ⟨R, rfl⟩, fun _ => ⟨_, rfl⟩⟩

theorem objMap_hyperRankG (U : Src.Object Src.γL M₀) : (objMap (ι := ι) U).hyperRankG = U.hyperRankG := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc h => rfl
  | hyper R => rfl

theorem mem_collMap_c2Can (C : CollData M₀) (Unsel : Set (Src.Object Src.γL M₀)) (U : Src.Object Src.γL M₀) :
    objMap (ι := ι) U ∈ (collMap ι C).C2Can L γ η w κ (objMap '' Unsel) ↔ U ∈ C.C2Can L γ η w κ Unsel := by
  unfold CollData.C2Can
  simp only [Set.mem_ofPred_eq, mem_collMap_c2Of]
  refine and_congr Iff.rfl ⟨fun h Q hQ hat hU hQh => ?_, fun h Q' hQ' hat hU hQh => ?_⟩
  · have := h (objMap Q) ((mem_collMap_c2Of ι C Unsel Q).mpr hQ) (by simpa using congrArg (Finset.map ι) hat)
      ((objMap_hyper_iff ι U).mpr hU) ((objMap_hyper_iff ι Q).mpr hQh)
    simpa [objMap_hyperRankG] using this
  · obtain ⟨Q, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) Q'
    have hQ := (mem_collMap_c2Of ι C Unsel Q).mp hQ'
    have := h Q hQ (Finset.map_injective ι (by simpa using hat)) ((objMap_hyper_iff ι U).mp hU)
      ((objMap_hyper_iff ι Q).mp hQh)
    simpa [objMap_hyperRankG] using this

theorem objMap_shape_vc_iff (U : Src.Object Src.γL M₀) :
    (∃ h, (objMap (ι := ι) U).shape = Src.VineLikeObject.vc h) ↔ ∃ h, U.shape = Src.VineLikeObject.vc h := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc h => exact ⟨fun _ => ⟨h, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  | hyper R => exact ⟨fun ⟨h, h'⟩ => (by cases h'), fun ⟨h, h'⟩ => (by cases h')⟩

/-! ### `SubproOblG` and `UnselOK` -/

theorem collMap_subproOblG (C : CollData M₀) :
    SubproOblG (collMap ι C) L γ η w κ ↔ SubproOblG C L γ η w κ := by
  have hpair : ∀ (v : V) (P : D₀ → D₀ → Prop), HasChosenPair ((collMap ι C).first (ι v)) ((collMap ι C).second (ι v)) P ↔
      HasChosenPair (C.first v) (C.second v) P := fun v P => hasChosenPair_map ι C v P
  constructor
  · intro h
    refine ⟨fun P hP hO hD => ?_, fun v hv => ?_, fun v hv (i : Fin C.n) hi => ?_, fun P hP hO hD => ?_⟩
    · exact (collMap_host ι C P).mp (h.contained (objMap P) ((objMap_hasGapKind_iff P L γ η w κ _).mpr hP)
        ((collMap_outside ι C P).mpr hO) ((collMap_disjoint_hinges ι C P).mpr hD))
    · have := h.hingeSG (ι v) (by simpa using hv)
      rw [hpair] at this
      exact (hasChosenPair_congr fun x y => by rw [tripleAtM_iff]).mp this
    · have := h.hingeJoint (ι v) (by simpa using hv) i (by
        simpa [ι.injective.eq_iff] using hi)
      rw [hpair] at this
      exact (hasChosenPair_congr fun x y => by rw [collMap_collection, objMap_containsDart_iff, objMap_containsDart_iff]).mp this
    · obtain ⟨v', hv', hvP, hrest⟩ := h.crossing (objMap P) ((objMap_hasGapKind_iff P L γ η w κ _).mpr hP)
        ((collMap_outside ι C P).mpr hO) (fun hd => hD ((collMap_disjoint_hinges ι C P).mp hd))
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (by simpa using hv')
      refine ⟨v, hv, by simpa using hvP, ?_⟩
      rcases hrest with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨fun e => h1 (by simp [e]), fun e => h2 (by simp [e])⟩
      · refine Or.inr ⟨?_, ?_⟩
        · rcases h1 with e | e
          · exact Or.inl (ι.injective e)
          · exact Or.inr (ι.injective e)
        · rw [hpair] at h2
          exact (hasChosenPair_congr fun x y => by rw [objMap_containsDart_iff, objMap_containsDart_iff]).mp h2
  · intro h
    refine ⟨fun P' hP hO hD => ?_, fun v' hv' => ?_, fun v' hv' (i : Fin C.n) hi => ?_, fun P' hP hO hD => ?_⟩
    · obtain ⟨P, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) P'
      exact (collMap_host ι C P).mpr (h.contained P ((objMap_hasGapKind_iff P L γ η w κ _).mp hP)
        ((collMap_outside ι C P).mp hO) ((collMap_disjoint_hinges ι C P).mp hD))
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (by simpa using hv')
      rw [hpair]
      exact (hasChosenPair_congr fun x y => by rw [tripleAtM_iff]).mpr (h.hingeSG v hv)
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (by simpa using hv')
      rw [hpair]
      exact (hasChosenPair_congr fun x y => by
        rw [collMap_collection, objMap_containsDart_iff, objMap_containsDart_iff]).mpr
        (h.hingeJoint v hv i (by simpa [collMap_collection, objMap_upper, objMap_lower, ι.injective.eq_iff] using hi))
    · obtain ⟨P, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) P'
      obtain ⟨v, hv, hvP, hrest⟩ := h.crossing P ((objMap_hasGapKind_iff P L γ η w κ _).mp hP)
        ((collMap_outside ι C P).mp hO) (fun hd => hD ((collMap_disjoint_hinges ι C P).mpr hd))
      refine ⟨ι v, by simpa using hv, by simpa using hvP, ?_⟩
      rcases hrest with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by simpa [ι.injective.eq_iff] using h1, by simpa [ι.injective.eq_iff] using h2⟩
      · refine Or.inr ⟨by simpa [ι.injective.eq_iff] using h1, ?_⟩
        rw [hpair]
        exact (hasChosenPair_congr fun x y => by rw [objMap_containsDart_iff, objMap_containsDart_iff]).mpr h2

theorem collMap_unselOK (C : CollData M₀) (Unsel : Set (Src.Object Src.γL M₀)) :
    (collMap ι C).UnselOK L γ η w κ (objMap '' Unsel) ↔ C.UnselOK L γ η w κ Unsel := by
  have hun : ∀ Q : Src.Object Src.γL M₀, objMap (ι := ι) Q ∈ objMap '' Unsel ↔ Q ∈ Unsel := fun Q =>
    ⟨fun ⟨Q2, h, e⟩ => objMap_injective e ▸ h, fun h => ⟨Q, h, rfl⟩⟩
  constructor
  · intro h
    refine ⟨fun B hB => ?_⟩
    obtain ⟨hP, hcase⟩ := h.dv (objMap B) ((hun B).mpr hB)
    refine ⟨(collMap_inP ι C B).mp hP, ?_⟩
    rcases hcase with ⟨U', hU', hsub⟩ | ⟨A', a', b', hσ, hA, hBv, hint, U', hU', hUA, hsh⟩
    · obtain ⟨U, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) U'
      exact Or.inl ⟨U, (mem_collMap_c2Can ι C Unsel U).mp hU', (Finset.map_subset_map (f := ι)).mp hsub⟩
    obtain ⟨A, a, b, rfl, rfl, rfl, hA2⟩ := exists_isSomeVine_of_mapAtoms M₀ ι hA
    obtain ⟨U, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) U'
    refine Or.inr ⟨A, a, b, (mapAtoms_bondsBetween M₀ ι a b).symm.trans hσ, hA2,
      (mapAtoms_isSomeVine M₀ ι B.atoms a b).mp hBv, ?_, U,
      (mem_collMap_c2Can ι C Unsel U).mp hU', Finset.map_injective ι hUA, (objMap_shape_vc_iff ι U).mp hsh⟩
    change Finset.map ι A ∩ Finset.map ι B.atoms = _ at hint
    rw [← Finset.map_inter] at hint
    exact Finset.map_injective ι (by rw [hint]; simp [Finset.map_insert])
  · intro h
    refine ⟨fun B' hB' => ?_⟩
    obtain ⟨B, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) B'
    obtain ⟨hP, hcase⟩ := h.dv B ((hun B).mp hB')
    refine ⟨(collMap_inP ι C B).mpr hP, ?_⟩
    rcases hcase with ⟨U, hU, hsub⟩ | ⟨A, a, b, hσ, hA, hBv, hint, U, hU, hUA, hsh⟩
    · exact Or.inl ⟨objMap U, (mem_collMap_c2Can ι C Unsel U).mpr hU, (Finset.map_subset_map (f := ι)).mpr hsub⟩
    refine Or.inr ⟨A.map ι, ι a, ι b, (mapAtoms_bondsBetween M₀ ι a b).trans hσ, (mapAtoms_isSomeVine M₀ ι A a b).mpr hA,
      (mapAtoms_isSomeVine M₀ ι B.atoms a b).mpr hBv, ?_, objMap U, (mem_collMap_c2Can ι C Unsel U).mpr hU,
      by simp [hUA], (objMap_shape_vc_iff ι U).mpr hsh⟩
    change Finset.map ι A ∩ Finset.map ι B.atoms = _
    rw [← Finset.map_inter, hint]; simp [Finset.map_insert]

/-- Every unselected set of `mapAtoms M₀ ι` is the image of one of `M₀`. -/
theorem collMap_unselOK' (C : CollData M₀) (Unsel' : Set (Src.Object Src.γL (mapAtoms M₀ ι))) :
    (collMap ι C).UnselOK L γ η w κ Unsel' ↔
      C.UnselOK L γ η w κ (objMap (ι := ι) ⁻¹' Unsel') := by
  rw [← collMap_unselOK ι C, Set.image_preimage_eq _ (objMap_surjective (M := M₀) (ι := ι))]

/-! ### Gap kinds at atoms, `DegenSGT`, `IsTame` -/

/-! ### Ladder-gap clause -/

end WaveTurbulence.GammaLow.FinalCount.H
