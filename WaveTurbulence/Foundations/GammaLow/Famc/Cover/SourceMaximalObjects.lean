/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.Spine.SourceCountingObjects
public import Mathlib.Data.Finset.Max
/-! Maximal designated SG objects cover every eligible non-omitted object. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceMaximalObjects` (sha256 55e3832f093864858c2dc93e4006e15f149451783f2c8874f634b0b694b955ed) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

private theorem object_contained_refl {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (P : Object γv M) : P.IsContained P := by
  rcases P with ⟨S, a, b, shape⟩
  cases shape with
  | vc h => exact Finset.Subset.refl S
  | hyper R => exact ⟨Finset.Subset.refl S, fun _ => Or.inl rfl⟩

private theorem object_contained_of_card_lt {V D : Type*} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} (P Q : Object γv M)
    (hsub : P.atoms ⊆ Q.atoms) (hlt : P.atoms.card < Q.atoms.card) : P.IsContained Q := by
  rcases P with ⟨A, x, y, P⟩
  rcases Q with ⟨S, a, b, Q⟩
  cases P <;> cases Q
  · exact hsub
  · exact hsub
  · exact hsub
  · exact ⟨hsub, fun he => False.elim ((Nat.ne_of_lt hlt) (congrArg Finset.card he))⟩

private theorem object_contained_reverse_of_atoms_eq {V D : Type*} [DecidableEq V]
    [Fintype D] [DecidableEq D] {M : Molecule V D} (P Q : Object γv M)
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
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)} {P : Object γv G.molecule}
    (h : eligibleSecondObject γv G L γ η base κ F P) :
    Disjoint (↑P.atoms : Set (GBranch G.tree)) F := by
  rcases h.2 with ⟨Q, hPQ, _, hQF⟩ | ⟨D, hPD, hDF⟩
  · exact disjointF_of_subset hPQ hQF
  · exact disjointF_of_subset hPD hDF

/-- Maximality uses atom cardinality while retaining equal-group hyper designations.
No transitivity of the designated containment predicate is assumed. -/
theorem exists_maximal_source_object {V D : Type*} [DecidableEq V] [Fintype V]
    [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Set (Object γv M))
    (P : Object γv M) (hP : P ∈ K) :
    ∃ Q ∈ K, P.IsContained Q ∧
      ∀ T ∈ K, Q.IsContained T → T.IsContained Q := by
  classical
  let : Fintype (Object γv M) := Fintype.ofFinite _
  let S : Finset (Object γv M) := univ.filter (fun Q => Q ∈ K ∧ P.IsContained Q)
  have hPS : P ∈ S := mem_filter.mpr ⟨mem_univ _, hP, object_contained_refl P⟩
  obtain ⟨Q, hQS, hmax⟩ := S.exists_max_image (fun Q => Q.atoms.card) ⟨P, hPS⟩
  obtain ⟨_, hQK, hPQ⟩ := mem_filter.mp hQS
  refine ⟨Q, hQK, hPQ, ?_⟩
  intro T hTK hQT
  have hsub := Object.contained_atoms_subset Q T hQT
  have hcard : T.atoms.card ≤ Q.atoms.card := by
    by_contra hle
    have hlt : Q.atoms.card < T.atoms.card := Nat.lt_of_not_ge hle
    have hPT := object_contained_of_card_lt P T
      ((Object.contained_atoms_subset P Q hPQ).trans hsub)
      ((Finset.card_le_card (Object.contained_atoms_subset P Q hPQ)).trans_lt hlt)
    have hTS : T ∈ S := mem_filter.mpr ⟨mem_univ _, hTK, hPT⟩
    exact (not_lt_of_ge (hmax T hTS)) hlt
  exact object_contained_reverse_of_atoms_eq Q T hQT
    (Finset.eq_of_subset_of_card_le hsub hcard)

/-- TARGET L2101–L2104: every eligible non-omitted object is contained in a selected maximal one. -/
theorem source_secondCollection_covers {w d : ℕ} (G : Garden w) (L γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) (F : Set (GBranch G.tree))
    (omitted : Set (Finset (GBranch G.tree))) (collection : Set (Object γv G.molecule))
    (hc : IsSourceSecondCollection γv G L γ η base κ F omitted collection)
    (P : Object γv G.molecule) (hp : eligibleSecondObject γv G L γ η base κ F P)
    (ho : P.atoms ∉ omitted) : ∃ Q ∈ collection, P.IsContained Q := by
  obtain ⟨Q, ⟨hQ, hQo⟩, hPQ, hmax⟩ := exists_maximal_source_object
    {Q : Object γv G.molecule | eligibleSecondObject γv G L γ η base κ F Q ∧ Q.atoms ∉ omitted}
    P ⟨hp, ho⟩
  refine ⟨Q, (hc.2.2 Q).mpr ⟨hQ, hQo, ?_⟩, hPQ⟩
  intro T hT hTo hQT
  exact hmax T ⟨hT, hTo⟩ hQT

end WaveTurbulence.GammaLow.Famc
