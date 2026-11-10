/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourcePrimaryPairChoices
public import WaveTurbulence.Foundations.Spine.SourcePairTableEncoding
public import WaveTurbulence.Foundations.Spine.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.Spine.SourceRestrictedCarrier
/-! TARGET L2108–L2112 requirements (d), (e) for C1, C2 and the hinges simultaneously: the pair
table extending `source_primary_pair_table` to the canonical restricted second collection. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset WaveTurbulence.Mole

/-- An unordered pair at `v` inside an object has an oriented version. -/
theorem exists_oriented_pair {w : ℕ} {G : Garden w} (P : Object G.molecule) {v : GBranch G.tree}
    {x y : GardenDart G} (hT : TripleAt G v x y) (hx : P.ContainsDart x) (hy : P.ContainsDart y) :
    ∃ xo yo, SourceObjectJointPair P v xo yo ∧ ((xo = x ∧ yo = y) ∨ (xo = y ∧ yo = x)) := by
  obtain ⟨h1, h2, _, hne⟩ := hT
  by_cases ho : G.molecule.out x = true
  · have : G.molecule.out y = false := by
      cases hy' : G.molecule.out y
      · rfl
      · exact absurd (ho.trans hy'.symm) hne
    exact ⟨x, y, ⟨h1, h2, hx, hy, ho, this⟩, Or.inl ⟨rfl, rfl⟩⟩
  · have hx' : G.molecule.out x = false := by simpa using ho
    have : G.molecule.out y = true := by
      cases hy' : G.molecule.out y
      · exact absurd (hx'.trans hy'.symm) hne
      · rfl
    exact ⟨y, x, ⟨h2, h1, hy, hx, this, hx'⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- A joint pair of one member of the canonical collection lies in every other member through
the same joint (requirement (f)(ii) is consistent). -/
theorem canonical_pair_transfer {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))}
    {K : Set (Object G.molecule)}
    (hK : IsSourceSecondCollection G L γ η base (bondIndex G z.1) F omitted K)
    (rk : GardenDart G → ℕ) (hrk : Function.Injective rk)
    {P Q : Object G.molecule} (hP : P ∈ canonicalSub rk K) (hQ : Q ∈ canonicalSub rk K)
    {v : GBranch G.tree} (hvP : v = P.upper ∨ v = P.lower) (hvQ : v = Q.upper ∨ v = Q.lower)
    {x y : GardenDart G} (hT : TripleAt G v x y) (hx : P.ContainsDart x) (hy : P.ContainsDart y) :
    Q.ContainsDart x ∧ Q.ContainsDart y := by
  have hk := spliced_molecule_decoration G hp hL base roots z
  have hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 →
      gardenSource G hp (fun i => base + latticePoint L (roots i)) v = 0 :=
    fun v _ hdeg => gardenSource_eq_zero_of_deg_four G hp _ v hdeg
  obtain ⟨hQsg, _⟩ := ((hK.2.2 Q).mp hQ.1).1
  obtain ⟨x', y', hT', hx', hy', _⟩ := source_actual_object_joint_sg_pair G hp hM Q hL γ η base
    roots z hQsg v hvQ
  obtain ⟨xo, yo, hpo, hor⟩ := exists_oriented_pair P hT hx hy
  obtain ⟨xo', yo', hpo', hor'⟩ := exists_oriented_pair Q hT' hx' hy'
  have heq := canonical_second_collection_pairs_compatible G hM hk hc hK rk hrk hP hQ hvP hvQ hpo hpo'
  obtain ⟨h1, h2⟩ := heq
  subst h1 h2
  have hQo := hpo'
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hQo.2.2.1, hQo.2.2.2.1⟩
  · exact ⟨hQo.2.2.2.1, hQo.2.2.1⟩

theorem source_full_pair_table {w d : ℕ} (G : Garden w) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (C : SubproChoices G) (hC : C.Structural)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z : GenDecoration G d roots 0)
    (kFix : Finset (Mom d))
    (hs : SubproSupport G C L γ η base kFix (bondIndex G z.1))
    {omitted : Set (Finset (GBranch G.tree))} {K : Set (Object G.molecule)}
    (hK : IsSourceSecondCollection G L γ η base (bondIndex G z.1) C.forbidden omitted K)
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
          P.ContainsDart x ∧ P.ContainsDart y)) := by
  classical
  obtain ⟨first, second, hsg, hh, hj⟩ := source_primary_pair_choices G hp hM C hC hL γ η
    base roots z kFix hs
  let K2 := canonicalSub rk K
  -- the C2 joints are outside the hinges and C1
  have hfar : ∀ P ∈ K2, ∀ v, (v = P.upper ∨ v = P.lower) →
      v ∉ C.hinges ∧ ∀ i, v ∉ (C.collection i).atoms := by
    intro P hP v hv
    have hvP := object_mem_of_joint P hv
    have hdis := eligible_atoms_disjoint ((hK.2.2 P).mp hP.1).1
    have hvF : (v : GBranch G.tree) ∉ C.forbidden := fun h =>
      Set.disjoint_left.mp hdis (Finset.mem_coe.mpr hvP) h
    refine ⟨fun h => hvF (Or.inl (Finset.mem_coe.mpr h)), fun i hi => hvF (Or.inr ?_)⟩
    exact Set.mem_iUnion.mpr ⟨i, Finset.mem_coe.mpr hi⟩
  have hlocal : ∀ v, ∃ a b : Option (GardenDart G),
      (atomGapKind G L γ η base (bondIndex G z.1) v = .SG → HasChosenPair a b (fun x y =>
        TripleAt G v x y ∧ Molecule.gapKind L γ η
          (Molecule.gapAt L base (bondIndex G z.1) x y) = .SG)) ∧
      (v ∈ C.hinges → a = C.first v ∧ b = C.second v) ∧
      (∀ i, (v = (C.collection i).upper ∨ v = (C.collection i).lower) →
        HasChosenPair a b (fun x y =>
          (C.collection i).ContainsDart x ∧ (C.collection i).ContainsDart y)) ∧
      (∀ P ∈ K2, (v = P.upper ∨ v = P.lower) →
        HasChosenPair a b (fun x y => P.ContainsDart x ∧ P.ContainsDart y)) := by
    intro v
    by_cases hex : ∃ P ∈ K2, (v = P.upper ∨ v = P.lower)
    · obtain ⟨P0, hP0, hv0⟩ := hex
      obtain ⟨hPsg, _⟩ := ((hK.2.2 P0).mp hP0.1).1
      obtain ⟨x, y, hT, hx, hy, hgap⟩ := source_actual_object_joint_sg_pair G hp hM P0 hL γ η
        base roots z hPsg v hv0
      obtain ⟨hnh, hn1⟩ := hfar P0 hP0 v hv0
      refine ⟨some x, some y, fun _ => ⟨x, y, rfl, rfl, hT, hgap⟩,
        fun h => absurd h hnh, fun i hi => ?_, fun P hP hvP => ?_⟩
      · exact absurd (object_mem_of_joint _ hi) (hn1 i)
      · obtain ⟨hx', hy'⟩ := canonical_pair_transfer G hp hM hL γ η base roots z hK rk hrk
          hP0 hP hv0 hvP hT hx hy
        exact ⟨x, y, rfl, rfl, hx', hy'⟩
    · exact ⟨first v, second v, hsg v, hh v, fun i hi => hj i v hi, fun P hP hv => absurd ⟨P, hP, hv⟩ hex⟩
  choose first2 second2 hsg2 hh2 hj2 hk2 using hlocal
  let first' := fun v => if atomGapKind G L γ η base (bondIndex G z.1) v = .SG then first2 v else none
  let second' := fun v => if atomGapKind G L γ η base (bondIndex G z.1) v = .SG then second2 v else none
  obtain ⟨T, hTf, hTs⟩ := exists_sourcePairTable G first' second' (by
    intro v
    by_cases hv : atomGapKind G L γ η base (bondIndex G z.1) v = .SG
    · obtain ⟨x, y, hx, hy, hxy, _⟩ := hsg2 v hv
      exact Or.inr ⟨x, y, by simpa only [first', ite_eq_left hv] using hx,
        by simpa only [second', ite_eq_left hv] using hy,
        (Mole.mem_dartsAt G.molecule v x).mpr hxy.1,
        (Mole.mem_dartsAt G.molecule v y).mpr hxy.2.1⟩
    · exact Or.inl ⟨by simp only [first', ite_eq_right hv], by simp only [second', ite_eq_right hv]⟩)
  refine ⟨T, ?_, ?_, ?_, ?_⟩
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

end WaveTurbulence.LGSpine
