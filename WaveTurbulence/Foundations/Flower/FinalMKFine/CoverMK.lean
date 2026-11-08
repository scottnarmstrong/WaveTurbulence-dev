/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKFine.FiberCount
import Mathlib.Tactic

/-! # C4b FINE-PIN: the counting cover with survivors (copy-thread of main's `Spine/Cover*`)

Main's cover (`CoverTags`, `CoverAdmissible`, `SourcePrimaryPairChoices`, `SourceFullPairTable`) with survivors:
- the second collection is selected outside `forbiddenMK Cs S` (Theorem 7.5′(7)): `tagChoiceMK`;
- dyadic atom scales only at `CriticalSGMK` atoms: `ScalesMK`, `fullChoiceMK`;
- the pair table also designates, at the first joint of each survivor, a pair of darts of that survivor
  (`AdmissibleMK`, 75-F1): `source_primary_pair_choicesMK`, `source_full_pair_tableMK`;
- `exists_cover_choiceMK`: every decoration with nonzero marked amplitude is `AdmissibleMK` for some
  (tag, scales);
- `countingGeometry_of_admissibleMK` and `hinges_card_le_numCriticalSGMK` (`q ≤ p` with survivors).

Copied by source from main (sha256 in `COPIED-SHA256SUMS`); the survivor clauses are new. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Mole
open Set Finset
open scoped Classical

variable {w d : ℕ}

/-- The tag-level counting choice with survivors (main's `tagChoice`, second collection outside `forbiddenMK`). -/
noncomputable def tagChoiceMK (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Cover.Tag G) :
    CountingChoices G d where
  subpro := Cs
  secondCollection :=
    canonicalSub (Cover.dartRank G) (Cover.secondOf G hM L γ η base (forbiddenMK Cs S) t.1).2
  omittedDVConstituents := (Cover.secondOf G hM L γ η base (forbiddenMK Cs S) t.1).1
  atomLabel := fun v => atomGapKind G L γ η base (Cover.kappaOf G L γ η base t.1) v
  first := sourcePairFirst G t.2
  second := sourcePairSecond G t.2
  atomScale := fun _ => 0
  ladderScale := fun _ => 0
  fixedRoots := univ.image (fun i => base + latticePoint L (roots i))

theorem tagChoiceMK_atomLabel (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Cover.Tag G)
    (v : GBranch G.tree) :
    (tagChoiceMK G hM Cs S L γ η base roots t).atomLabel v =
      atomGapKind G L γ η base (Cover.kappaOf G L γ η base t.1) v := by
  unfold tagChoiceMK
  rfl

theorem secondOKMK_tag (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Cover.Tag G)
    (κ : GardenDart G → (Fin d → ℤ))
    (hK : IsSourceSecondCollection G L γ η base κ (forbiddenMK Cs S)
      (Cover.secondOf G hM L γ η base (forbiddenMK Cs S) t.1).1
      (Cover.secondOf G hM L γ η base (forbiddenMK Cs S) t.1).2)
    (as : GBranch G.tree → ℝ) (ls : Finset (GBranch G.tree) → ℝ) :
    SecondCollectionOKMK ({tagChoiceMK G hM Cs S L γ η base roots t with atomScale := as, ladderScale := ls} :
      CountingChoices G d) S L γ η base κ := by
  unfold tagChoiceMK
  exact ⟨Cover.dartRank G, Cover.dartRank_injective G, _, hK, rfl⟩

theorem tagChoiceMK_with_atomLabel (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (t : Cover.Tag G)
    (as : GBranch G.tree → ℝ) (ls : Finset (GBranch G.tree) → ℝ) (v : GBranch G.tree) :
    ({tagChoiceMK G hM Cs S L γ η base roots t with atomScale := as, ladderScale := ls} :
      CountingChoices G d).atomLabel v = atomGapKind G L γ η base (Cover.kappaOf G L γ η base t.1) v := by
  unfold tagChoiceMK
  rfl

theorem criticalSG_with {G : Garden w} (B : CountingChoices G d) (as : GBranch G.tree → ℝ)
    (ls : Finset (GBranch G.tree) → ℝ) (v : GBranch G.tree) :
    ({B with atomScale := as, ladderScale := ls} : CountingChoices G d).CriticalSG v ↔ B.CriticalSG v :=
  Iff.rfl

theorem ladderGaps_with {G : Garden w} (B : CountingChoices G d) (as : GBranch G.tree → ℝ)
    (ls : Finset (GBranch G.tree) → ℝ) (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) :
    ({B with atomScale := as, ladderScale := ls} : CountingChoices G d).LadderGaps L γ η base κ ↔
      ({B with ladderScale := ls} : CountingChoices G d).LadderGaps L γ η base κ :=
  Iff.rfl

/-- The dyadic scale data with survivors: one per maximal ladder and per `CriticalSGMK` atom. -/
abbrev ScalesMK {G : Garden w} (B : CountingChoices G d) (S : SurvivorData G) (L γ η : ℝ) :=
  Cover.LadderChoices G L × ({v // CriticalSGMK B S v} → Cover.AtomScale L γ η)

/-- The full counting choice of a tag with survivor scales. -/
noncomputable def fullChoiceMK {G : Garden w} (B : CountingChoices G d) (S : SurvivorData G) {L γ η : ℝ}
    (s : ScalesMK B S L γ η) : CountingChoices G d :=
  { B with
    atomScale := fun v => if h : CriticalSGMK B S v then (s.2 ⟨v, h⟩).1 else 0
    ladderScale := fun S' => if h : S' ∈ G.molecule.maximalLadders then
      (match s.1 ⟨S', h⟩ with | none => 0 | some P => P.1) else 0 }

theorem fullChoiceMK_numCritical {G : Garden w} (B : CountingChoices G d) (S : SurvivorData G) {L γ η : ℝ}
    (s : ScalesMK B S L γ η) : numCriticalSGMK (fullChoiceMK B S s) S = numCriticalSGMK B S := rfl

theorem exists_scalesMK_of_admissible {G : Garden w} (B : CountingChoices G d) (S : SurvivorData G)
    {L γ η : ℝ} (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) (as : GBranch G.tree → ℝ)
    (ls : Finset (GBranch G.tree) → ℝ)
    (h : AdmissibleMK ({B with atomScale := as, ladderScale := ls} : CountingChoices G d) S L γ η base κ) :
    ∃ s : ScalesMK B S L γ η, AdmissibleMK (fullChoiceMK B S s) S L γ η base κ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have hat : ∀ v, CriticalSGMK B S v → IsDyadicScale (as v) ∧ L⁻¹ ≤ as v ∧ as v ≤ L ^ (-γ + η) :=
    fun v hv => ⟨(h9 v hv).1, (h9 v hv).2.1, (h9 v hv).2.2.1⟩
  have hla : ∀ S' ∈ G.molecule.maximalLadders, ls S' ≠ 0 →
      IsDyadicScale (ls S') ∧ L⁻¹ ≤ ls S' ∧ ls S' ≤ 1 :=
    fun S' hS h0 => ((h10 S' hS).1).resolve_left h0
  let f : Cover.LadderChoices G L := fun S' =>
    if h0 : ls S'.1 = 0 then none else some ⟨ls S'.1, hla S'.1 S'.2 h0⟩
  let g : {v // CriticalSGMK B S v} → Cover.AtomScale L γ η := fun v => ⟨as v.1, hat v.1 v.2⟩
  refine ⟨(f, g), h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_⟩
  · intro v hv
    have hv' : CriticalSGMK B S v := hv
    have := h9 v hv'
    simpa only [fullChoiceMK, hv', dite_true, g] using this
  · intro S' hS
    have hagree : (fullChoiceMK B S (f, g)).ladderScale S' = ls S' := by
      simp only [fullChoiceMK, hS, dite_true, f]
      by_cases h0 : ls S' = 0
      · simp [h0]
      · simp [h0]
    have := h10 S' hS
    simpa only [hagree] using this

/-- At most one survivor has `v` as its first joint. -/
theorem survFirstJoint_unique {G : Garden w} {S : SurvivorData G} {i j : Fin S.m} {v : GBranch G.tree}
    (hi : SurvFirstJoint S i v) (hj : SurvFirstJoint S j v) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hi.1 (hj.2 i h)
  · exact h
  · exact absurd hj.1 (hi.2 j h)

/-- Main's `source_primary_pair_choices` with survivors: hinges and `C₁` joints as on main, and at the first joint
of a survivor a pair of its darts (from `SubproSupportMK.jointPair` at hinges, from its SG joint pair otherwise). -/
theorem source_primary_pair_choicesMK (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (C : SubproChoices G) (hC : C.Structural) (S : SurvivorData G)
    (hS : S.Structural C) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) (kFix : Finset (Mom d))
    (hs : SubproSupportMK G C S L γ η base kFix (bondIndex G z.1)) :
    ∃ first second : GBranch G.tree → Option (GardenDart G),
      (∀ v, atomGapKind G L γ η base (bondIndex G z.1) v = .SG →
        HasChosenPair (first v) (second v) (fun x y => TripleAt G v x y ∧
          Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG)) ∧
      (∀ v ∈ C.hinges, first v = C.first v ∧ second v = C.second v) ∧
      (∀ i v, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
        HasChosenPair (first v) (second v) (fun x y =>
          (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) ∧
      (∀ i v, SurvFirstJoint S i v →
        HasChosenPair (first v) (second v) (fun x y =>
          (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) := by
  let SG := fun v x y => TripleAt G v x y ∧
    Molecule.gapKind L γ η (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG
  let Joint := fun v i => v = (C.collection i).upper ∨ v = (C.collection i).lower
  have hjunique : ∀ v i j, Joint v i → Joint v j → i = j := by
    intro v i j hi hj
    by_contra hne
    exact Finset.disjoint_left.mp (hC.2.1 i j hne)
      (object_mem_of_joint _ hi) (object_mem_of_joint _ hj)
  have hlocal : ∀ v, ∃ a b : Option (GardenDart G),
      (atomGapKind G L γ η base (bondIndex G z.1) v = .SG → HasChosenPair a b (SG v)) ∧
      (v ∈ C.hinges → a = C.first v ∧ b = C.second v) ∧
      (∀ i, Joint v i → HasChosenPair a b (fun x y =>
        (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) ∧
      (∀ i, SurvFirstJoint S i v → HasChosenPair a b (fun x y =>
        (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) := by
    intro v
    by_cases hh : v ∈ C.hinges
    · exact ⟨C.first v, C.second v, fun _ => hs.hingeSG v hh, fun _ => ⟨rfl, rfl⟩,
        fun i hi => hs.hingeJoint v hh i hi, fun i hi => hs.jointPair i v hi⟩
    · by_cases hj : ∃ i, Joint v i
      · obtain ⟨i, hi⟩ := hj
        obtain ⟨x, y, hxy, hx, hy, hsg⟩ := source_actual_object_joint_sg_pair G hp hM
          (C.collection i) hL γ η base roots z (hs.selectedSG i) v hi
        refine ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hxy, hsg⟩,
          fun hv => False.elim (hh hv), ?_, ?_⟩
        · intro j hj
          have he := hjunique v i j hi hj
          subst j
          exact ⟨x, y, rfl, rfl, hx, hy⟩
        · intro j hj
          exact False.elim (Finset.disjoint_left.mp (hS.2.1 i j) (object_mem_of_joint _ hi)
            (object_mem_of_joint _ hj.1))
      · by_cases hsj : ∃ i, SurvFirstJoint S i v
        · obtain ⟨i, hi⟩ := hsj
          obtain ⟨x, y, hxy, hx, hy, hsg⟩ := source_actual_object_joint_sg_pair G hp hM
            (S.surv i) hL γ η base roots z (hs.survivorSG i) v hi.1
          refine ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hxy, hsg⟩,
            fun hv => False.elim (hh hv), fun i' hi' => False.elim (hj ⟨i', hi'⟩), ?_⟩
          intro j hj'
          have he := survFirstJoint_unique hi hj'
          subst j
          exact ⟨x, y, rfl, rfl, hx, hy⟩
        · by_cases hsg : atomGapKind G L γ η base (bondIndex G z.1) v = .SG
          · obtain ⟨x, y, hxy⟩ := (source_atomGapKind_eq_SG_iff G L γ η base _ v).mp hsg
            exact ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hxy⟩,
              fun hv => False.elim (hh hv), fun i hi => False.elim (hj ⟨i, hi⟩),
              fun i hi => False.elim (hsj ⟨i, hi⟩)⟩
          · exact ⟨none, none, fun hv => False.elim (hsg hv),
              fun hv => False.elim (hh hv), fun i hi => False.elim (hj ⟨i, hi⟩),
              fun i hi => False.elim (hsj ⟨i, hi⟩)⟩
  choose first second hsg hhinge hfirst hsurv using hlocal
  exact ⟨first, second, hsg, hhinge, fun i v hv => hfirst v i hv, fun i v hv => hsurv v i hv⟩

/-- Main's `source_full_pair_table` with survivors (second collection outside `forbiddenMK`). -/
theorem source_full_pair_tableMK (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (C : SubproChoices G) (hC : C.Structural) (S : SurvivorData G)
    (hS : S.Structural C) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0) (kFix : Finset (Mom d))
    (hs : SubproSupportMK G C S L γ η base kFix (bondIndex G z.1))
    {omitted : Set (Finset (GBranch G.tree))} {K : Set (Object G.molecule)}
    (hK : IsSourceSecondCollection G L γ η base (bondIndex G z.1) (forbiddenMK C S) omitted K)
    (rk : GardenDart G → ℕ) (hrk : Function.Injective rk) :
    ∃ T : SourcePairTable G,
      (∀ v, atomGapKind G L γ η base (bondIndex G z.1) v = .SG →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          TripleAt G v x y ∧ Molecule.gapKind L γ η
            (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG)) ∧
      (∀ v ∈ C.hinges, sourcePairFirst G T v = C.first v ∧
        sourcePairSecond G T v = C.second v) ∧
      (∀ i v, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) ∧
      (∀ P ∈ canonicalSub rk K, ∀ v, (v = P.upper ∨ v = P.lower) →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          P.ContainsDart x ∧ P.ContainsDart y)) ∧
      (∀ i v, SurvFirstJoint S i v →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) := by
  obtain ⟨first, second, hsg, hh, hj, hsv⟩ := source_primary_pair_choicesMK G hp hM C hC S hS hL γ η
    base roots z kFix hs
  let K2 := canonicalSub rk K
  have hfar : ∀ P ∈ K2, ∀ v, (v = P.upper ∨ v = P.lower) →
      v ∉ C.hinges ∧ (∀ i, v ∉ (C.collection i).atoms) ∧ ∀ i, v ∉ (S.surv i).atoms := by
    intro P hP v hv
    have hvP := object_mem_of_joint P hv
    have hdis := eligible_atoms_disjoint ((hK.2.2 P).mp hP.1).1
    have hvF : (v : GBranch G.tree) ∉ forbiddenMK C S := fun h =>
      Set.disjoint_left.mp hdis (Finset.mem_coe.mpr hvP) h
    refine ⟨fun h => hvF (Or.inl (Or.inl (Finset.mem_coe.mpr h))), fun i hi => hvF (Or.inl (Or.inr ?_)),
      fun i hi => hvF (Or.inr ?_)⟩
    · exact Set.mem_iUnion.mpr ⟨i, Finset.mem_coe.mpr hi⟩
    · exact Set.mem_iUnion.mpr ⟨i, Finset.mem_coe.mpr hi⟩
  have hlocal : ∀ v, ∃ a b : Option (GardenDart G),
      (atomGapKind G L γ η base (bondIndex G z.1) v = .SG → HasChosenPair a b (fun x y =>
        TripleAt G v x y ∧ Molecule.gapKind L γ η
          (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG)) ∧
      (v ∈ C.hinges → a = C.first v ∧ b = C.second v) ∧
      (∀ i, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
        HasChosenPair a b (fun x y =>
          (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) ∧
      (∀ P ∈ K2, (v = P.upper ∨ v = P.lower) →
        HasChosenPair a b (fun x y => P.ContainsDart x ∧ P.ContainsDart y)) ∧
      (∀ i, SurvFirstJoint S i v →
        HasChosenPair a b (fun x y => (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y)) := by
    intro v
    by_cases hex : ∃ P ∈ K2, (v = P.upper ∨ v = P.lower)
    · obtain ⟨P0, hP0, hv0⟩ := hex
      obtain ⟨hPsg, _⟩ := ((hK.2.2 P0).mp hP0.1).1
      obtain ⟨x, y, hT, hx, hy, hgap⟩ := source_actual_object_joint_sg_pair G hp hM P0 hL γ η
        base roots z hPsg v hv0
      obtain ⟨hnh, hn1, hn2⟩ := hfar P0 hP0 v hv0
      refine ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hT, hgap⟩,
        fun h => absurd h hnh, fun i hi => ?_, fun P hP hvP => ?_, fun i hi => ?_⟩
      · exact absurd (object_mem_of_joint _ hi) (hn1 i)
      · obtain ⟨hx', hy'⟩ := canonical_pair_transfer G hp hM hL γ η base roots z hK rk hrk
          hP0 hP hv0 hvP hT hx hy
        exact ⟨x, y, rfl, rfl, hx', hy'⟩
      · exact absurd (object_mem_of_joint _ hi.1) (hn2 i)
    · exact ⟨first v, second v, hsg v, hh v, fun i hi => hj i v hi,
        fun P hP hv => absurd ⟨P, hP, hv⟩ hex, fun i hi => hsv i v hi⟩
  choose first2 second2 hsg2 hh2 hj2 hk2 hs2 using hlocal
  let first' := fun v =>
    if atomGapKind G L γ η base (bondIndex G z.1) v = .SG then first2 v else none
  let second' := fun v =>
    if atomGapKind G L γ η base (bondIndex G z.1) v = .SG then second2 v else none
  obtain ⟨T, hTf, hTs⟩ := exists_sourcePairTable G first' second' (by
    intro v
    by_cases hv : atomGapKind G L γ η base (bondIndex G z.1) v = .SG
    · obtain ⟨x, y, hx, hy, hxy, _⟩ := hsg2 v hv
      exact Or.inr ⟨x, y, by simpa only [first', ite_eq_left hv] using hx,
        by simpa only [second', ite_eq_left hv] using hy,
        (Mole.mem_dartsAt G.molecule v x).mpr hxy.1,
        (Mole.mem_dartsAt G.molecule v y).mpr hxy.2.1⟩
    · exact Or.inl ⟨by simp only [first', ite_eq_right hv], by simp only [second', ite_eq_right hv]⟩)
  refine ⟨T, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hv] using hsg2 v hv
  · intro v hv
    have hkind : atomGapKind G L γ η base (bondIndex G z.1) v = .SG := by
      obtain ⟨x, y, _, _, hxy⟩ := hs.hingeSG v hv
      exact (source_atomGapKind_eq_SG_iff G L γ η base _ v).mpr ⟨x, y, hxy⟩
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hh2 v hv
  · intro i v hv
    have hkind := source_actual_object_joint_is_SG G hp hM (C.collection i) hL γ η
      base roots z (hs.selectedSG i) v hv
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hj2 v i hv
  · intro P hP v hv
    have hkind := source_actual_object_joint_is_SG G hp hM P hL γ η
      base roots z ((hK.2.2 P).mp hP.1).1.1 v hv
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hk2 v P hP hv
  · intro i v hv
    have hkind := source_actual_object_joint_is_SG G hp hM (S.surv i) hL γ η
      base roots z (hs.survivorSG i) v hv.1
    rw [hTf, hTs]
    simpa only [first', second', ite_eq_left hkind] using hs2 v i hv

/-- Assembly of `AdmissibleMK` for a tag choice from the pair table and the two scale families. -/
theorem admissibleMK_of_table (G : Garden w) (hM : G.molecule.IsMolecule) (Cs : SubproChoices G)
    (S : SurvivorData G) (L γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (κ : GardenDart G → (Fin d → ℤ)) (τ : SourceAtomPair G → Molecule.GapKind) (T : SourcePairTable G)
    (hsup : SubproSupportMK G Cs S L γ η base (Finset.univ.image fun i => base + latticePoint L (roots i)) κ)
    (hK : IsSourceSecondCollection G L γ η base κ (forbiddenMK Cs S)
      (Cover.secondOf G hM L γ η base (forbiddenMK Cs S) τ).1
      (Cover.secondOf G hM L γ η base (forbiddenMK Cs S) τ).2)
    (hlabel : ∀ v, atomGapKind G L γ η base κ v = atomGapKind G L γ η base (Cover.kappaOf G L γ η base τ) v)
    (hT1 : ∀ v, atomGapKind G L γ η base κ v = .SG →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          TripleAt G v x y ∧ Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = .SG))
    (hT2 : ∀ v ∈ Cs.hinges, sourcePairFirst G T v = Cs.first v ∧ sourcePairSecond G T v = Cs.second v)
    (hT3 : ∀ i v, (v = (Cs.collection i).upper ∨ v = (Cs.collection i).lower) →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          (Cs.collection i).ContainsDart x ∧ (Cs.collection i).ContainsDart y))
    (hT4 : ∀ P ∈ canonicalSub (Cover.dartRank G) (Cover.secondOf G hM L γ η base (forbiddenMK Cs S) τ).2,
        ∀ v, (v = P.upper ∨ v = P.lower) →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          P.ContainsDart x ∧ P.ContainsDart y))
    (hT5 : ∀ i v, SurvFirstJoint S i v →
        HasChosenPair (sourcePairFirst G T v) (sourcePairSecond G T v) (fun x y =>
          (S.surv i).ContainsDart x ∧ (S.surv i).ContainsDart y))
    (as : GBranch G.tree → ℝ)
    (has : ∀ v, (tagChoiceMK G hM Cs S L γ η base roots (τ, T)).CriticalSG v →
      IsDyadicScale (as v) ∧ L⁻¹ ≤ as v ∧ as v ≤ L ^ (-γ + η) ∧
        HasChosenPair ((tagChoiceMK G hM Cs S L γ η base roots (τ, T)).first v)
          ((tagChoiceMK G hM Cs S L γ η base roots (τ, T)).second v) (fun x y =>
          as v / 2 ≤ ‖Molecule.gapAt L base κ x y‖ ∧ ‖Molecule.gapAt L base κ x y‖ ≤ 2 * as v))
    (ls : Finset (GBranch G.tree) → ℝ)
    (hls : ({tagChoiceMK G hM Cs S L γ η base roots (τ, T) with ladderScale := ls} :
      CountingChoices G d).LadderGaps L γ η base κ) :
    AdmissibleMK ({tagChoiceMK G hM Cs S L γ η base roots (τ, T) with atomScale := as, ladderScale := ls} :
      CountingChoices G d) S L γ η base κ := by
  have h2 := secondOKMK_tag G hM Cs S L γ η base roots (τ, T) κ hK as ls
  refine ⟨hsup, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [tagChoiceMK_with_atomLabel]
    exact hlabel v
  · intro v hv
    rw [tagChoiceMK_with_atomLabel] at hv
    exact hT1 v ((hlabel v).trans hv)
  · exact hT2
  · exact hT3
  · exact hT5
  · exact hT4
  · intro v hv
    exact has v ((criticalSG_with _ as ls v).mp hv.1)
  · exact (ladderGaps_with _ as ls L γ η base κ).mpr hls

theorem atomLabel_of_table (G : Garden w) (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (τ : SourceAtomPair G → Molecule.GapKind) (hτ : sourceGapTable G L γ η base κ = τ) (v : GBranch G.tree) :
    atomGapKind G L γ η base κ v = atomGapKind G L γ η base (Cover.kappaOf G L γ η base τ) v :=
  sourceGapTable_atomGapKind_eq G L γ η base κ _
    (hτ.trans (Cover.kappaOf_table G L γ η base τ κ hτ).symm) v

/-- **The cover with survivors**: every decoration with nonzero marked amplitude is `AdmissibleMK` for a
(tag, survivor scales). -/
theorem exists_cover_choiceMK {R : ℕ} (G : Garden (2 * R)) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) (Cs : SubproChoices G) (S : SurvivorData G)
    {L : ℝ} (hL : 2 ≤ L) (γ η : ℝ) (hcap : 2 * L⁻¹ ≤ L ^ (-γ + η)) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ))
    (hS : SubproConclusionsMK G D.toSplicedKernelData Cs S L γ η base roots)
    (z : GenDecoration G d roots 0) (hz : ampMK G D L γ η base z.1 ≠ 0) :
    ∃ (t : Cover.Tag G) (s : ScalesMK (tagChoiceMK G hM Cs S L γ η base roots t) S L γ η),
      AdmissibleMK (fullChoiceMK _ S s) S L γ η base (bondIndex G z.1) := by
  have hL0 : L ≠ 0 := by linarith
  have hamp := amp_ne_zero_of_ampMK hz
  obtain ⟨he, hg, _⟩ := splicedMomentumAmplitude_support G _ hD L γ η base z.1 hamp
  have hsup := hS.support z he hg
  obtain ⟨τ, hτ⟩ : ∃ τ, sourceGapTable G L γ η base (bondIndex G z.1) = τ := ⟨_, rfl⟩
  have hK := Cover.secondOf_spec G hM L γ η base (forbiddenMK Cs S) τ (bondIndex G z.1) hτ
  obtain ⟨T, hT1, hT2, hT3, hT4, hT5⟩ := source_full_pair_tableMK G hp hM Cs hS.structural S
    hS.survivors hL0 γ η base roots z _ hsup hK (Cover.dartRank G) (Cover.dartRank_injective G)
  have hlabel := atomLabel_of_table G L γ η base (bondIndex G z.1) τ hτ
  obtain ⟨as, has⟩ := exists_counting_atomScales G (tagChoiceMK G hM Cs S L γ η base roots (τ, T))
    (by linarith) γ η hcap base (bondIndex G z.1) (by
      intro v hv
      rw [tagChoiceMK_atomLabel, ← hlabel] at hv
      obtain ⟨x, y, hx, hy, _, hgap⟩ := hT1 v hv
      exact ⟨x, y, hx, hy, hgap⟩)
  obtain ⟨ls, hls⟩ := exists_counting_ladderScales G (tagChoiceMK G hM Cs S L γ η base roots (τ, T))
    hL γ η base (bondIndex G z.1)
  have hadm := admissibleMK_of_table G hM Cs S L γ η base roots (bondIndex G z.1) τ T hsup hK hlabel
    hT1 hT2 hT3 hT4 hT5 as has ls hls
  obtain ⟨s, hs⟩ := exists_scalesMK_of_admissible _ S base (bondIndex G z.1) as ls hadm
  exact ⟨(τ, T), s, hs⟩

/-- Main's `coverIndex_geometry_of_subpro_choices` for a marked admissible witness. -/
theorem countingGeometry_of_admissibleMK {R : ℕ} (G : Garden (2 * R)) (hgeo : SplicedGeomPremises G)
    (D : SplicedKernelData G d) (C : CountingChoices G d) (S : SurvivorData G) {L γ η : ℝ} (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (hS : SubproConclusionsMK G D C.subpro S L γ η base roots)
    (hfix : C.fixedRoots = Finset.univ.image (fun i => base + latticePoint L (roots i)))
    (κ : GardenDart G → (Fin d → ℤ)) (hadm : AdmissibleMK C S L γ η base κ) :
    CountingGeometry G C := by
  refine ⟨hgeo.molecule, hgeo.connected, hgeo.atom_count, hgeo.bond_count, hS.structural, ?_, ?_,
    hS.hingeOutsideFirst, ?_, hS.tripleDesignated, hS.hingeNoLoop⟩
  · rw [hfix]
    exact (Finset.card_image_le).trans (by simp)
  · intro v hv
    rw [← hadm.2.2.1 v]
    obtain ⟨x, y, _, _, hxy⟩ := hadm.1.hingeSG v hv
    exact (source_atomGapKind_eq_SG_iff G L γ η base _ v).mpr ⟨x, y, hxy⟩
  · obtain ⟨rk, _, K, hK, hC⟩ := hadm.2.1
    intro v hv P hP hi
    rw [hC] at hP
    have hdis := eligible_atoms_disjoint ((hK.2.2 P).mp hP.1).1
    exact Set.disjoint_left.mp hdis (Finset.mem_coe.mpr hi.1) (Or.inl (Or.inl (Finset.mem_coe.mpr hv)))

/-- `q ≤ p` with survivors: every hinge is a critical SG atom outside the survivors' interiors. -/
theorem hinges_card_le_numCriticalSGMK {R : ℕ} {G : Garden (2 * R)} {C : CountingChoices G d}
    {S : SurvivorData G} (h : CountingGeometry G C) (hS : S.Structural C.subpro) :
    C.subpro.hinges.card ≤ numCriticalSGMK C S := by
  unfold numCriticalSGMK
  apply Finset.card_le_card
  intro v hv
  exact mem_filter.mpr ⟨mem_univ _, ⟨h.hingeSmall v hv, h.hingeOutsideFirst v hv,
    h.hingeOutsideSecond v hv⟩, fun i => hS.2.2.2 v hv i⟩

end WaveTurbulence.Flower.FinalMKFine
