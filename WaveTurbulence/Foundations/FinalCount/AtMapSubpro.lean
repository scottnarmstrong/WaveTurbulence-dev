/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AtMapObject
public import WaveTurbulence.Foundations.FinalCount.AtMapCount
public import WaveTurbulence.Foundations.FinalCount.G3FinalE3
public import WaveTurbulence.Foundations.FinalCount.G3VineLG1
public import WaveTurbulence.Foundations.FinalCount.VCSource
import Mathlib.Tactic

/-! # ATOM-TRANSPORT, part 5: the collection data and the named obligations of `subpro`

`collMap ι C` is the collection data (`C₁`, hinges, designated pairs) of `mapAtoms M₀ ι` obtained from those of
`M₀`.  `SubproOblG`, `UnselOK` (with `C2Of`), `DegenSGT`, `SGat`, `IsTame`, `SourceLadderGaps` hold for the
transported data iff they hold for the original (both directions; every object of `mapAtoms M₀ ι` is an
`objMap`, so every unselected set of `mapAtoms M₀ ι` is the image of one of `M₀`). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.AtomTransport
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

theorem tripleAtM_iff (v : V) (x y : D₀) : TripleAtM (mapAtoms M₀ ι) (ι v) x y ↔ TripleAtM M₀ v x y := by
  simp [TripleAtM, ι.injective.eq_iff]

theorem hasChosenPair_map (C : CollData M₀) (v : V) (P : D₀ → D₀ → Prop) :
    HasChosenPair ((collMap ι C).first (ι v)) ((collMap ι C).second (ι v)) P ↔
      HasChosenPair (C.first v) (C.second v) P := by
  rw [collMap_first, collMap_second]

theorem collMap_outside (C : CollData M₀) (P : Object M₀) :
    (collMap ι C).Outside (objMap P) ↔ C.Outside P := by
  unfold CollData.Outside
  exact forall_congr' fun i => not_congr Finset.map_subset_map

theorem collMap_disjoint_hinges (C : CollData M₀) (P : Object M₀) :
    Disjoint (objMap (ι := ι) P).atoms (collMap ι C).hinges ↔ Disjoint P.atoms C.hinges := by
  simp [Finset.disjoint_map]

theorem collMap_host (C : CollData M₀) (P : Object M₀) :
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

theorem collMap_inP (C : CollData M₀) (P : Object M₀) :
    (collMap ι C).InP L γ η w κ (objMap P) ↔ C.InP L γ η w κ P := by
  unfold CollData.InP
  rw [objMap_hasGapKind_iff, collMap_outside, collMap_disjoint_hinges, collMap_host]

theorem mem_collMap_c2Of (C : CollData M₀) (Unsel : Set (Object M₀)) (U : Object M₀) :
    objMap (ι := ι) U ∈ (collMap ι C).C2Of L γ η w κ (objMap '' Unsel) ↔ U ∈ C.C2Of L γ η w κ Unsel := by
  have hun : ∀ Q : Object M₀, objMap (ι := ι) Q ∈ objMap '' Unsel ↔ Q ∈ Unsel := fun Q =>
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

theorem objMap_hyper_iff (U : Object M₀) :
    (∃ R, (objMap (ι := ι) U).shape = VineLikeObject.hyper R) ↔ ∃ R, U.shape = VineLikeObject.hyper R := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc h => exact ⟨fun ⟨R, h'⟩ => (by cases h'), fun ⟨R, h'⟩ => (by cases h')⟩
  | hyper R => exact ⟨fun _ => ⟨R, rfl⟩, fun _ => ⟨_, rfl⟩⟩

theorem objMap_hyperRankG (U : Object M₀) : (objMap (ι := ι) U).hyperRankG = U.hyperRankG := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc h => rfl
  | hyper R => rfl

theorem mem_collMap_c2Can (C : CollData M₀) (Unsel : Set (Object M₀)) (U : Object M₀) :
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

theorem objMap_shape_vc_iff (U : Object M₀) :
    (∃ h, (objMap (ι := ι) U).shape = VineLikeObject.vc h) ↔ ∃ h, U.shape = VineLikeObject.vc h := by
  obtain ⟨S, a, b, sh⟩ := U
  cases sh with
  | vc h => exact ⟨fun _ => ⟨h, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  | hyper R => exact ⟨fun ⟨h, h'⟩ => (by cases h'), fun ⟨h, h'⟩ => (by cases h')⟩

theorem hasChosenPair_congr {E : Type*} {f s : Option E} {P Q : E → E → Prop} (h : ∀ x y, P x y ↔ Q x y) :
    HasChosenPair f s P ↔ HasChosenPair f s Q := by
  unfold HasChosenPair
  exact exists_congr fun x => exists_congr fun y => and_congr Iff.rfl (and_congr Iff.rfl (h x y))

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

theorem collMap_unselOK (C : CollData M₀) (Unsel : Set (Object M₀)) :
    (collMap ι C).UnselOK L γ η w κ (objMap '' Unsel) ↔ C.UnselOK L γ η w κ Unsel := by
  have hun : ∀ Q : Object M₀, objMap (ι := ι) Q ∈ objMap '' Unsel ↔ Q ∈ Unsel := fun Q =>
    ⟨fun ⟨Q2, h, e⟩ => objMap_injective e ▸ h, fun h => ⟨Q, h, rfl⟩⟩
  constructor
  · intro h
    refine ⟨fun B hB => ?_⟩
    obtain ⟨hP, hcase⟩ := h.dv (objMap B) ((hun B).mpr hB)
    refine ⟨(collMap_inP ι C B).mp hP, ?_⟩
    rcases hcase with ⟨U', hU', hsub⟩ | ⟨A', a', b', hA, hBv, hint, U', hU', hUA, hsh⟩
    · obtain ⟨U, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) U'
      exact Or.inl ⟨U, (mem_collMap_c2Can ι C Unsel U).mp hU', (Finset.map_subset_map (f := ι)).mp hsub⟩
    obtain ⟨A, a, b, rfl, rfl, rfl, hA2⟩ := exists_isVine_of_mapAtoms M₀ ι hA
    obtain ⟨U, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) U'
    refine Or.inr ⟨A, a, b, hA2, (mapAtoms_isVine M₀ ι _ B.atoms a b).mp hBv, ?_, U,
      (mem_collMap_c2Can ι C Unsel U).mp hU', Finset.map_injective ι hUA, (objMap_shape_vc_iff ι U).mp hsh⟩
    change Finset.map ι A ∩ Finset.map ι B.atoms = _ at hint
    rw [← Finset.map_inter] at hint
    exact Finset.map_injective ι (by rw [hint]; simp [Finset.map_insert])
  · intro h
    refine ⟨fun B' hB' => ?_⟩
    obtain ⟨B, rfl⟩ := objMap_surjective (M := M₀) (ι := ι) B'
    obtain ⟨hP, hcase⟩ := h.dv B ((hun B).mp hB')
    refine ⟨(collMap_inP ι C B).mpr hP, ?_⟩
    rcases hcase with ⟨U, hU, hsub⟩ | ⟨A, a, b, hA, hBv, hint, U, hU, hUA, hsh⟩
    · exact Or.inl ⟨objMap U, (mem_collMap_c2Can ι C Unsel U).mpr hU, (Finset.map_subset_map (f := ι)).mpr hsub⟩
    refine Or.inr ⟨A.map ι, ι a, ι b, (mapAtoms_isVine M₀ ι _ A a b).mpr hA,
      (mapAtoms_isVine M₀ ι _ B.atoms a b).mpr hBv, ?_, objMap U, (mem_collMap_c2Can ι C Unsel U).mpr hU,
      by simp [hUA], (objMap_shape_vc_iff ι U).mpr hsh⟩
    change Finset.map ι A ∩ Finset.map ι B.atoms = _
    rw [← Finset.map_inter, hint]; simp [Finset.map_insert]

/-- Every unselected set of `mapAtoms M₀ ι` is the image of one of `M₀`. -/
theorem collMap_unselOK' (C : CollData M₀) (Unsel' : Set (Object (mapAtoms M₀ ι))) :
    (collMap ι C).UnselOK L γ η w κ Unsel' ↔
      C.UnselOK L γ η w κ (objMap (ι := ι) ⁻¹' Unsel') := by
  rw [← collMap_unselOK ι C, Set.image_preimage_eq _ (objMap_surjective (M := M₀) (ι := ι))]

/-! ### Gap kinds at atoms, `DegenSGT`, `IsTame` -/

theorem mapAtoms_sgat (a : V) :
    SGat (mapAtoms M₀ ι) L γ η w κ (ι a) ↔ SGat M₀ L γ η w κ a := by
  unfold SGat
  simp only [mapAtoms_atom, mapAtoms_out, mapAtoms_mate, ι.injective.eq_iff]

theorem mapAtoms_degenSGT (Tm' : W → Prop) :
    DegenSGT (mapAtoms M₀ ι) L γ η w κ Tm' ↔ DegenSGT M₀ L γ η w κ (fun a => Tm' (ι a)) := by
  unfold DegenSGT
  constructor
  · intro h a ha x y hx hy hxo hyo hne hz
    have := h (ι a) ((Finset.mem_map' ι).mpr ha) x y (by simp [hx]) (by simp [hy]) hxo hyo hne hz
    rwa [mapAtoms_sgat] at this
  · intro h a' ha' x y hx hy hxo hyo hne hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp ha'
    have hx' : M₀.atom x = a := ι.injective hx
    have hy' : M₀.atom y = a := ι.injective hy
    rw [mapAtoms_sgat]
    exact h a ha x y hx' hy' hxo hyo hne hz

theorem mapAtoms_isTame (L : ℝ) (w : Mom d) (kFix : Finset (Mom d)) (a : V) :
    (mapAtoms M₀ ι).IsTame L w kFix κ (ι a) ↔ M₀.IsTame L w kFix κ a := by
  unfold Molecule.IsTame
  simp only [mapAtoms_atom, ι.injective.eq_iff, mapAtoms_deg]

/-! ### Ladder-gap clause -/

theorem mapAtoms_sourceLadderGaps (P' : Finset W → ℝ) :
    SourceLadderGaps (mapAtoms M₀ ι) L w P' κ ↔
      SourceLadderGaps M₀ L w (fun S => P' (S.map ι)) κ := by
  unfold SourceLadderGaps
  rw [mapAtoms_maximalLadders]
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun S _ => and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨m, u', v', hm, hl, hat, r, hr, h0, h1, h2⟩
    obtain ⟨u, v, rfl, rfl, hl0⟩ := exists_ladder_of_mapAtoms M₀ ι u' v' hl
    rw [mapAtoms_ladderAtoms] at hat
    exact ⟨m, u, v, hm, hl0, Finset.map_injective ι hat, r, (mapAtoms_isLadderGap M₀ ι L w κ u v hm r).mp hr,
      h0, h1, h2⟩
  · rintro ⟨m, u, v, hm, hl, hat, r, hr, h0, h1, h2⟩
    exact ⟨m, _, _, hm, (mapAtoms_isLadder M₀ ι u v).mpr hl, by rw [mapAtoms_ladderAtoms, hat], r,
      (mapAtoms_isLadderGap M₀ ι L w κ u v hm r).mpr hr, h0, h1, h2⟩

/-- The ladder scale of `mapAtoms M ι` induced by a scale `P` of `M`: `P` of the preimage. -/
noncomputable def scaleMap (P : Finset V → ℝ) (S' : Finset W) : ℝ :=
  P (S'.preimage ι ι.injective.injOn)

theorem scaleMap_map (P : Finset V → ℝ) (S : Finset V) : scaleMap ι P (S.map ι) = P S := by
  unfold scaleMap
  rw [Finset.preimage_map]

theorem mapAtoms_sourceLadderGaps_scaleMap (P : Finset V → ℝ) :
    SourceLadderGaps (mapAtoms M₀ ι) L w (scaleMap ι P) κ ↔ SourceLadderGaps M₀ L w P κ := by
  rw [mapAtoms_sourceLadderGaps]
  simp only [scaleMap_map]

end WaveTurbulence.AtomTransport
