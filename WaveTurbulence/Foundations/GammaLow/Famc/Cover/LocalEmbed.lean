/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.Spine.SourceVineSigma
/-! # `𝒱_γ` membership is local to the atomic group (packet L5c)

Main's `Molecule/VineLocalDartObjects.lean` / `VineLocalDartChains.lean` transport the drawn vines and their chains
along a local dart embedding (an identification of all darts internal to `A`, e.g. the erasure of a bond outside
the group). The D11 definitions of `IsTVine` (block, multiplicities inside `S`, the closure built from `groupNbrs`,
`groupBonds` and `σ`) only see darts internal to `S`, so T-vines, `𝒱_enl`, `𝒱_γ` and L6's `Src.Chain` transport
too. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.GammaLow.FinalCount.Src

variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E] [DecidableEq D] [DecidableEq E]
    {M : Molecule V D} {N : Molecule V E} {A : Finset V}

theorem embed_bondsBetween_eq (F : Vine.LocalDartEmbedding M N A) {S : Finset V} (hSA : S ⊆ A) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) : N.bondsBetween u v = M.bondsBetween u v := by
  rw [LGSpine.bondsBetween_eq_count_groupBonds hu hv, LGSpine.bondsBetween_eq_count_groupBonds hu hv,
    F.groupBonds_eq S hSA]

theorem embed_groupNbrs_eq (F : Vine.LocalDartEmbedding M N A) (S : Finset V) (hSA : S ⊆ A) (v : V) :
    N.groupNbrs S v = M.groupNbrs S v := by
  classical
  let f : E ↪ D := ⟨F.toFun, F.injective⟩
  have hmap : ((N.dartsAt v).filter fun x => N.InGroup S x).map f =
      (M.dartsAt v).filter fun x => M.InGroup S x := by
    ext d
    constructor
    · intro hd
      obtain ⟨e, he, rfl⟩ := mem_map.mp hd
      obtain ⟨he1, hg⟩ := mem_filter.mp he
      refine mem_filter.mpr ⟨?_, (F.inGroup_iff S e).mpr hg⟩
      simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and] at he1 ⊢
      exact (F.atom_eq e).trans he1
    · intro hd
      obtain ⟨hd1, hg⟩ := mem_filter.mp hd
      obtain ⟨e, he⟩ := F.surjective_internal d ⟨hSA hg.1, hSA hg.2⟩
      refine mem_map.mpr ⟨e, mem_filter.mpr ⟨?_, ?_⟩, he⟩
      · simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and] at hd1 ⊢
        rw [← F.atom_eq, show F.toFun e = d from he]
        exact hd1
      · apply (F.inGroup_iff S e).mp
        rw [show F.toFun e = d from he]
        exact hg
  unfold Molecule.groupNbrs
  rw [← hmap, Finset.map_val, Multiset.map_map]
  congr 1
  funext e
  exact (F.neighbor_eq e).symm

theorem embed_isClosure_iff (F : Vine.LocalDartEmbedding M N A) {S : Finset V} (hSA : S ⊆ A) {j₁ j₂ : V}
    (h₁ : j₁ ∈ S) (h₂ : j₂ ∈ S) (G : TVine.UMultigraph V) :
    N.IsClosure S j₁ j₂ G ↔ M.IsClosure S j₁ j₂ G := by
  unfold Molecule.IsClosure Molecule.sigma
  rw [embed_bondsBetween_eq F hSA h₁ h₂, embed_groupNbrs_eq F S hSA j₁, embed_groupNbrs_eq F S hSA j₂,
    F.groupBonds_eq S hSA]

/-- **T-vines are local**: a local dart embedding identifying the internal darts of `S` preserves `IsTVine`. -/
theorem embed_isTVine_iff (F : Vine.LocalDartEmbedding M N A) {S : Finset V} (hSA : S ⊆ A) (a b : V) :
    N.IsTVine S a b ↔ M.IsTVine S a b := by
  constructor
  · rintro ⟨hB, h2, G, G', hcl, hr, hT⟩
    refine ⟨(F.isBlock_iff S hSA a b).mp hB, fun u hu v hv huv => ?_, G, G',
      (embed_isClosure_iff F hSA hB.2.1 hB.2.2.1 G).mp hcl, hr, hT⟩
    rw [← embed_bondsBetween_eq F hSA hu hv]
    exact h2 u hu v hv huv
  · rintro ⟨hB, h2, G, G', hcl, hr, hT⟩
    refine ⟨(F.isBlock_iff S hSA a b).mpr hB, fun u hu v hv huv => ?_, G, G',
      (embed_isClosure_iff F hSA hB.2.1 hB.2.2.1 G).mpr hcl, hr, hT⟩
    rw [embed_bondsBetween_eq F hSA hu hv]
    exact h2 u hu v hv huv

theorem embed_isVineGamma_iff (F : Vine.LocalDartEmbedding M N A) {γ : ℝ} {S : Finset V} (hSA : S ⊆ A)
    (a b : V) : N.IsVineGamma γ S a b ↔ M.IsVineGamma γ S a b := by
  unfold Molecule.IsVineGamma Molecule.IsVineEnl
  rw [F.isVine_iff .I S hSA a b, F.isVine_iff .II S hSA a b, embed_isTVine_iff F hSA a b]
  constructor
  · rintro (h | ⟨hγ, X, hX⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hγ, X, (F.isVine_iff X S hSA a b).mp hX⟩
  · rintro (h | ⟨hγ, X, hX⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hγ, X, (F.isVine_iff X S hSA a b).mpr hX⟩

/-- Every original `𝒱_γ` chain lifts through an identification of all its internal darts (main's
`LocalDartEmbedding.chain_of`). -/
theorem embed_chain_of (F : Vine.LocalDartEmbedding M N A) {γ : ℝ} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain γ M S a b n) : S ⊆ A → Chain γ N S a b n := by
  induction h with
  | single h =>
    intro hSA
    exact Chain.single ((embed_isVineGamma_iff F hSA _ _).mpr h)
  | @append S T a b c n hS hT hi hne ih =>
    intro hUA
    exact Chain.append (ih (Finset.subset_union_left.trans hUA))
      ((embed_isVineGamma_iff F (Finset.subset_union_right.trans hUA) _ _).mpr hT) hi hne

end WaveTurbulence.GammaLow.Famc
