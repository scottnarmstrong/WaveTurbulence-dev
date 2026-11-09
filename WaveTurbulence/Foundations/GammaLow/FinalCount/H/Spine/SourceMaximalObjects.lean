/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceMaximalObjects`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Maximal designated SG objects cover every eligible non-omitted object. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

private theorem object_contained_refl {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (P : Src.Object Src.γL M) : P.IsContained P := by
  rcases P with ⟨S, a, b, shape⟩
  cases shape with
  | vc h => exact Finset.Subset.refl S
  | hyper R => exact ⟨Finset.Subset.refl S, fun _ => Or.inl rfl⟩

private theorem object_contained_of_card_lt {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (P Q : Src.Object Src.γL M)
    (hsub : P.atoms ⊆ Q.atoms) (hlt : P.atoms.card < Q.atoms.card) : P.IsContained Q := by
  rcases P with ⟨A, x, y, P⟩
  rcases Q with ⟨S, a, b, Q⟩
  cases P <;> cases Q
  · exact hsub
  · exact hsub
  · exact hsub
  · exact ⟨hsub, fun he => False.elim ((Nat.ne_of_lt hlt) (congrArg Finset.card he))⟩

private theorem object_contained_reverse_of_atoms_eq {V D : Type*} [DecidableEq V]
    [Fintype D] [DecidableEq D] {M : Molecule V D} (P Q : Src.Object Src.γL M)
    (h : P.IsContained Q) (he : P.atoms = Q.atoms) : Q.IsContained P := by
  have hs : Q.atoms ⊆ P.atoms := by rw [he]
  rcases P with ⟨A, x, y, P⟩
  rcases Q with ⟨S, a, b, Q⟩
  cases P with
  | vc hP => cases Q <;> exact hs
  | hyper R =>
    cases Q with
    | vc hQ => exact hs
    | hyper T =>
      refine ⟨hs, fun _ => ?_⟩
      rcases h.2 he with hd | hd
      · exact Or.inl hd.symm
      · exact Or.inr (by rw [hd, M.mate_mate])

theorem eligible_atoms_disjoint {w d : ℕ} {G : Garden w} {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)} {P : Src.Object Src.γL G.molecule}
    (h : Src.eligibleSecondObject Src.γL G L γ η base κ F P) :
    Disjoint (↑P.atoms : Set (GBranch G.tree)) F := by
  rcases h.2 with ⟨Q, hPQ, _, hQF⟩ | ⟨D, hPD, hDF⟩
  · exact disjointF_of_subset hPQ hQF
  · exact disjointF_of_subset hPD hDF

/-- Maximality uses atom cardinality while retaining equal-group hyper designations.
No transitivity of the designated containment predicate is assumed. -/
theorem exists_maximal_source_object {V D : Type*} [DecidableEq V] [Fintype V]
    [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Set (Src.Object Src.γL M))
    (P : Src.Object Src.γL M) (hP : P ∈ K) :
    ∃ Q ∈ K, P.IsContained Q ∧
      ∀ T ∈ K, Q.IsContained T → T.IsContained Q := by
  classical
  let : Fintype (Src.Object Src.γL M) := Fintype.ofFinite _
  let S : Finset (Src.Object Src.γL M) := univ.filter (fun Q => Q ∈ K ∧ P.IsContained Q)
  have hPS : P ∈ S := mem_filter.mpr ⟨mem_univ _, hP, object_contained_refl P⟩
  obtain ⟨Q, hQS, hmax⟩ := S.exists_max_image (fun Q => Q.atoms.card) ⟨P, hPS⟩
  obtain ⟨_, hQK, hPQ⟩ := mem_filter.mp hQS
  refine ⟨Q, hQK, hPQ, ?_⟩
  intro T hTK hQT
  have hsub := Q.contained_atoms_subset T hQT
  have hcard : T.atoms.card ≤ Q.atoms.card := by
    by_contra hle
    have hlt : Q.atoms.card < T.atoms.card := Nat.lt_of_not_ge hle
    have hPT := object_contained_of_card_lt P T
      ((P.contained_atoms_subset Q hPQ).trans hsub)
      ((Finset.card_le_card (P.contained_atoms_subset Q hPQ)).trans_lt hlt)
    have hTS : T ∈ S := mem_filter.mpr ⟨mem_univ _, hTK, hPT⟩
    exact (not_lt_of_ge (hmax T hTS)) hlt
  exact object_contained_reverse_of_atoms_eq Q T hQT
    (Finset.eq_of_subset_of_card_le hsub hcard)

/-- TARGET L2101–L2104: every eligible non-omitted object is contained in a selected maximal one. -/
theorem source_secondCollection_covers {w d : ℕ} (G : Garden w) (L γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) (F : Set (GBranch G.tree))
    (omitted : Set (Finset (GBranch G.tree))) (collection : Set (Src.Object Src.γL G.molecule))
    (hc : Src.IsSourceSecondCollection Src.γL G L γ η base κ F omitted collection)
    (P : Src.Object Src.γL G.molecule) (hp : Src.eligibleSecondObject Src.γL G L γ η base κ F P)
    (ho : P.atoms ∉ omitted) : ∃ Q ∈ collection, P.IsContained Q := by
  obtain ⟨Q, ⟨hQ, hQo⟩, hPQ, hmax⟩ := exists_maximal_source_object
    {Q : Src.Object Src.γL G.molecule | Src.eligibleSecondObject Src.γL G L γ η base κ F Q ∧ Q.atoms ∉ omitted}
    P ⟨hp, ho⟩
  refine ⟨Q, (hc.2.2 Q).mpr ⟨hQ, hQo, ?_⟩, hPQ⟩
  intro T hT hTo hQT
  exact hmax T ⟨hT, hTo⟩ hQT

end WaveTurbulence.GammaLow.FinalCount.H
