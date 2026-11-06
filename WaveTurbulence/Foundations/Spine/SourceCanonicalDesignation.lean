/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourcePairsMain
public import WaveTurbulence.Foundations.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.Spine.SourceCanonicalDef
/-! R6(a): pair compatibility and covering for the canonical part of the second collection. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The canonical part still covers every atom set of the collection (and keeps the hyper
shape). -/
theorem canonicalSub_covers [Fintype V] {M : Molecule V D} (rk : D → ℕ) (K : Set (Object M))
    (P : Object M) (hP : P ∈ K) :
    ∃ Q ∈ canonicalSub rk K, Q.atoms = P.atoms ∧
      ((∃ R, P.shape = .hyper R) → ∃ R, Q.shape = .hyper R) := by
  classical
  by_cases hh : ∃ R, P.shape = .hyper R
  · let : Fintype (Object M) := Fintype.ofFinite _
    let S : Finset (Object M) :=
      Finset.univ.filter (fun Q => Q ∈ K ∧ Q.atoms = P.atoms ∧ ∃ R, Q.shape = .hyper R)
    have hPS : P ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP, rfl, hh⟩
    obtain ⟨Q, hQS, hmin⟩ := S.exists_min_image (fun Q => Q.hyperRank rk) ⟨P, hPS⟩
    obtain ⟨_, hQK, hQat, hQh⟩ := Finset.mem_filter.mp hQS
    refine ⟨Q, ⟨hQK, fun Q' hQ' hat _ hQ'h => ?_⟩, hQat, fun _ => hQh⟩
    exact hmin Q' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ', hat.trans hQat, hQ'h⟩)
  · refine ⟨P, ⟨hP, fun _ _ _ h => absurd h hh⟩, rfl, fun h => absurd h hh⟩

theorem hyper_bond_eq_of_rank_eq {M : Molecule V D} (rk : D → ℕ) (hrk : Function.Injective rk)
    {P Q : Object M} {R : HyperLikeRealization M P.atoms P.upper P.lower}
    {R' : HyperLikeRealization M Q.atoms Q.upper Q.lower}
    (hP : P.shape = .hyper R) (hQ : Q.shape = .hyper R')
    (h : P.hyperRank rk = Q.hyperRank rk) :
    R'.added = R.added ∨ R'.added = M.mate R.added := by
  unfold Object.hyperRank at h
  rw [hP, hQ] at h
  simp only at h
  have hm : ∀ x, M.mate (M.mate x) = x := M.mate_mate
  rcases min_choice (rk R.added) (rk (M.mate R.added)) with h1 | h1 <;>
    rcases min_choice (rk R'.added) (rk (M.mate R'.added)) with h2 | h2 <;>
    rw [h1, h2] at h
  · exact Or.inl (hrk h).symm
  · right
    have := hrk h
    rw [this, hm]
  · right
    exact (hrk h).symm
  · left
    have := hrk h
    have := congrArg M.mate this
    rw [hm, hm] at this
    exact this.symm

/-- R6(a): with one canonical designation per atom set, two members of the second collection
sharing a joint use the same dart pair there; the exceptional disjunct of
`source_second_collection_pairs_compatible` is gone. -/
theorem canonical_second_collection_pairs_compatible {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))}
    {collection : Set (Object G.molecule)}
    (hc : IsSourceSecondCollection G L γ η base κ F omitted collection)
    (rk : GardenDart G → ℕ) (hrk : Function.Injective rk)
    {P Q : Object G.molecule} (hPm : P ∈ canonicalSub rk collection)
    (hQm : Q ∈ canonicalSub rk collection)
    {v : GBranch G.tree} (hvP : v = P.upper ∨ v = P.lower) (hvQ : v = Q.upper ∨ v = Q.lower)
    {x y x' y' : GardenDart G}
    (hxy : SourceObjectJointPair P v x y) (hxy' : SourceObjectJointPair Q v x' y') :
    x = x' ∧ y = y' := by
  rcases source_second_collection_pairs_compatible G hM hκ hc0 hc hPm.1 hQm.1 hvP hvQ hxy hxy'
    with h | ⟨hat, ⟨R, hR⟩, ⟨R', hR'⟩⟩
  · exact h
  · have h1 := hPm.2 Q hQm.1 hat.symm ⟨R, hR⟩ ⟨R', hR'⟩
    have h2 := hQm.2 P hPm.1 hat ⟨R', hR'⟩ ⟨R, hR⟩
    have hb := hyper_bond_eq_of_rank_eq rk hrk hR hR' (le_antisymm h1 h2)
    have hconv : ∀ z, Q.ContainsDart z → P.ContainsDart z := by
      intro z hz
      unfold Object.ContainsDart at hz ⊢
      rw [hR'] at hz
      rw [hR]
      simp only at hz ⊢
      obtain ⟨a1, a2, a3⟩ := hz
      refine ⟨?_, ?_, hat ▸ a3⟩
      · rcases hb with e | e
        · rw [← e]; exact a1
        · intro hz'; apply a2; rw [e, G.molecule.mate_mate]; exact hz'
      · rcases hb with e | e
        · rw [← e]; exact a2
        · rw [← e]; exact a1
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hxy'
    exact source_object_joint_pair_unique P hvP hxy ⟨b1, b2, hconv _ b3, hconv _ b4, b5, b6⟩

end WaveTurbulence.LGSpine
