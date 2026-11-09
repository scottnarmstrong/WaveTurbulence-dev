/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.Molecule.VineLocalDartObjects
public import WaveTurbulence.Foundations.Molecule.VineLocalDartErasure
import Mathlib.Tactic
/-! # `𝒱_γ` is local: invariance under internal dart identifications (packet L5a, item C)

Main's `Vine.LocalDartEmbedding.isVine_iff` (`Molecule/VineLocalDartObjects.lean`) transports the drawn vine
predicates along an identification of the darts internal to an atom set (e.g. deleting a bond outside it,
`eraseBond_local_embedding`). This module adds the same for the D11 predicates: the number of bonds between two atoms
of the set, the neighbour multisets `groupNbrs`, the closure `IsClosure`, `IsTVine`, and hence `IsVineGamma`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open Finset

variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E]

/-- The bonds between two atoms of `S` are counted by the group bonds of `S`. -/
theorem bondsBetween_eq_count (M : Molecule V D) {S : Finset V} {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    M.bondsBetween u v = (M.groupBonds S).count s(u, v) := by
  classical
  unfold Molecule.bondsBetween Molecule.groupBonds
  rw [Multiset.count_map, ← Finset.filter_val, Finset.card_val]
  congr 1
  ext x
  simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ho, he⟩
    refine ⟨⟨ho, ?_⟩, he.symm⟩
    unfold Molecule.ends at he
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ hu, h2 ▸ hv⟩
    · exact ⟨h1 ▸ hv, h2 ▸ hu⟩
  · rintro ⟨⟨ho, -⟩, he⟩
    exact ⟨ho, he.symm⟩

namespace LocalDart
variable {M : Molecule V D} {N : Molecule V E} {A : Finset V} (F : Vine.LocalDartEmbedding M N A)
include F

theorem bondsBetween_eq {u v : V} (hu : u ∈ A) (hv : v ∈ A) : N.bondsBetween u v = M.bondsBetween u v := by
  rw [bondsBetween_eq_count N hu hv, bondsBetween_eq_count M hu hv, F.groupBonds_eq A (subset_refl A)]

theorem groupNbrs_eq (S : Finset V) (hSA : S ⊆ A) (v : V) : N.groupNbrs S v = M.groupNbrs S v := by
  classical
  let f : E ↪ D := ⟨F.toFun, F.injective⟩
  let U := (N.dartsAt v).filter fun x => N.InGroup S x
  let T := (M.dartsAt v).filter fun x => M.InGroup S x
  have hmap : U.map f = T := by
    ext d
    constructor
    · intro hd
      obtain ⟨e, he, rfl⟩ := mem_map.mp hd
      obtain ⟨hev, hg⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v _).mpr ((F.atom_eq e).trans ((Mole.mem_dartsAt N v e).mp hev)),
        (F.inGroup_iff S e).mpr hg⟩
    · intro hd
      obtain ⟨hdv, hg⟩ := mem_filter.mp hd
      obtain ⟨e, he⟩ := F.surjective_internal d ⟨hSA hg.1, hSA hg.2⟩
      refine mem_map.mpr ⟨e, mem_filter.mpr ⟨?_, ?_⟩, he⟩
      · apply (Mole.mem_dartsAt N v e).mpr
        rw [← F.atom_eq, he]
        exact (Mole.mem_dartsAt M v d).mp hdv
      · apply (F.inGroup_iff S e).mp
        rwa [he]
  unfold Molecule.groupNbrs
  change U.val.map (fun x => N.atom (N.mate x)) = T.val.map (fun x => M.atom (M.mate x))
  rw [← hmap, Finset.map_val, Multiset.map_map]
  congr 1
  funext e
  exact (F.neighbor_eq e).symm

theorem isClosure_iff (S : Finset V) (hSA : S ⊆ A) {j₁ j₂ : V} (h₁ : j₁ ∈ S) (h₂ : j₂ ∈ S)
    (G : TVine.UMultigraph V) : N.IsClosure S j₁ j₂ G ↔ M.IsClosure S j₁ j₂ G := by
  unfold Molecule.IsClosure Molecule.sigma
  rw [bondsBetween_eq F (hSA h₁) (hSA h₂), groupNbrs_eq F S hSA j₁, groupNbrs_eq F S hSA j₂,
    F.groupBonds_eq S hSA]

theorem isTVine_iff (S : Finset V) (hSA : S ⊆ A) (a b : V) : N.IsTVine S a b ↔ M.IsTVine S a b := by
  constructor
  · rintro ⟨hB, hm, G, G', hc, hr, ht⟩
    refine ⟨(F.isBlock_iff S hSA a b).mp hB, fun u hu v hv huv => ?_, G, G',
      (isClosure_iff F S hSA hB.2.1 hB.2.2.1 G).mp hc, hr, ht⟩
    rw [← bondsBetween_eq F (hSA hu) (hSA hv)]
    exact hm u hu v hv huv
  · rintro ⟨hB, hm, G, G', hc, hr, ht⟩
    refine ⟨(F.isBlock_iff S hSA a b).mpr hB, fun u hu v hv huv => ?_, G, G',
      (isClosure_iff F S hSA hB.2.1 hB.2.2.1 G).mpr hc, hr, ht⟩
    rw [bondsBetween_eq F (hSA hu) (hSA hv)]
    exact hm u hu v hv huv

/-- **`𝒱_γ` is local** (main's `LocalDartEmbedding.isVine_iff`, for the D11 family). -/
theorem isVineGamma_iff (γ : ℝ) (S : Finset V) (hSA : S ⊆ A) (a b : V) :
    N.IsVineGamma γ S a b ↔ M.IsVineGamma γ S a b := by
  unfold Molecule.IsVineGamma Molecule.IsVineEnl
  simp only [F.isVine_iff _ S hSA a b, isTVine_iff F S hSA a b]

end LocalDart

/-- A member of `𝒱_γ` stays a member after deleting a bond outside its group. -/
theorem isSomeVine_eraseBond {γ : ℝ} {M : Molecule V D} (e : D) {S : Finset V} {x y : V}
    (hv : FinalCount.Src.IsSomeVine γ M S x y) (h : ¬ M.InGroup S e) :
    FinalCount.Src.IsSomeVine γ (Molecule.eraseBond M e) S x y :=
  (LocalDart.isVineGamma_iff (Vine.eraseBond_local_embedding M e S h) γ S (subset_refl S) x y).mpr hv

/-- A member of `𝒱_γ` after deleting a bond outside its group is a member of the molecule. -/
theorem isSomeVine_of_eraseBond {γ : ℝ} {M : Molecule V D} (e : D) {S : Finset V} {x y : V}
    (hv : FinalCount.Src.IsSomeVine γ (Molecule.eraseBond M e) S x y) (h : ¬ M.InGroup S e) :
    FinalCount.Src.IsSomeVine γ M S x y :=
  (LocalDart.isVineGamma_iff (Vine.eraseBond_local_embedding M e S h) γ S (subset_refl S) x y).mp hv

end WaveTurbulence.GammaLow.Fama
