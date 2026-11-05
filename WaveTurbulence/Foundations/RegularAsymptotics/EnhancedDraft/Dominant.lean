/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Enhanced

/-!
# Dominant couples: the B2 draft against DH21 Def 4.17 (packet C5)

DH21 Def 3.? (`deflegal`, L739) and Prop 3.4 (L752): a regular chain with branching nodes
`𝔫_1, …, 𝔫_{2m}` (top to bottom) carries a legal partition `𝒫` of `{1, …, 2m}`; the chain is
**dominant** if `𝒫 = {{1,2}, …, {2m-1, 2m}}`. DH21 Def 4.17 (`defstd`, L854): `×` is dominant; a
couple `𝒬 ≠ ×` is dominant if `𝒬₀` is a `(1,1)`-mini couple or a double chain of two dominant
chains, and every `𝒬_j` replacing a leaf pair of `𝒬₀` is dominant.

* `chainPartition X o`: the partition coded by a chain (Catalan form `pair m Qr Qg inner rest` pairs
  `𝔫_{o+1}` with `𝔫_{o+2+2·|inner|}`), listed in increasing first element;
* `partition_dominant_iff`: every pair is `{a, a+1}` iff every `inner` on the spine is empty;
* `dominant_iff_source`: the draft's Boolean `RegCpl.dominant` is DH21 Def 4.17 literally
  (`DominantSrc`: condition (i) on the partitions of the two chains, condition (ii) on all the
  replacing couples `𝒬_{j,ε,ι}` and `𝒬_lp`, recursively).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

/-- The number of pairs of a chain code (half its number of chain nodes). -/
def chainPairs : RegChain → ℕ
  | .nil => 0
  | .pair _ _ _ inner rest => chainPairs inner + chainPairs rest + 1

/-- **The legal partition of a chain code** (DH21 Prop 3.4), with chain nodes numbered from
`o + 1`: the first node is paired with the node after the `2·|inner|` nodes of `inner`. -/
def chainPartition : RegChain → ℕ → List (ℕ × ℕ)
  | .nil, _ => []
  | .pair _ _ _ inner rest, o =>
    (o + 1, o + 2 * chainPairs inner + 2) :: chainPartition inner (o + 1) ++
      chainPartition rest (o + 2 * chainPairs inner + 2)

/-- `𝒫` is dominant (DH21 `deflegal`): all its pairs are `{a, a + 1}`. -/
def PartitionDominant (P : List (ℕ × ℕ)) : Prop := ∀ p ∈ P, p.2 = p.1 + 1

/-- The spine condition: every pair of the chain is formed by consecutive nodes. -/
def spineDominant : RegChain → Bool
  | .nil => true
  | .pair _ _ _ inner rest => inner.isNil && spineDominant rest

theorem chainPairs_eq_zero_iff (X : RegChain) : chainPairs X = 0 ↔ X.isNil = true := by
  cases X <;> simp [chainPairs, RegChain.isNil]

/-- **A chain is dominant iff its partition is `{{1,2}, …, {2m-1, 2m}}`.** -/
theorem partition_dominant_iff : (X : RegChain) → (o : ℕ) →
    PartitionDominant (chainPartition X o) ↔ spineDominant X = true
  | .nil, o => by simp [PartitionDominant, chainPartition, spineDominant]
  | .pair m Qr Qg inner rest, o => by
    have hr := partition_dominant_iff rest (o + 2 * chainPairs inner + 2)
    simp only [PartitionDominant, chainPartition, List.mem_cons, List.mem_append,
      spineDominant, Bool.and_eq_true] at hr ⊢
    constructor
    · intro h
      have h0 := h _ (Or.inl (Or.inl rfl))
      have hi : chainPairs inner = 0 := by simp at h0; omega
      have hin : inner = .nil := by cases inner <;> simp_all [chainPairs]
      subst hin
      exact ⟨rfl, hr.1 fun p hp => h p (Or.inr hp)⟩
    · rintro ⟨hn, hs⟩
      have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
      subst hin
      rintro p ((rfl | hp) | hp)
      · simp [chainPairs]
      · simp [chainPartition] at hp
      · exact hr.2 hs p hp

mutual
/-- **Dominant couples, DH21 Def 4.17 literally**: `×`; type 1 (`𝒬₀` a `(1,1)`-mini couple) with
dominant `𝒬₁, 𝒬₂, 𝒬₃`; type 2 with dominant partitions `𝒫^±` and dominant replacing couples. -/
def DominantSrc : RegCpl → Prop
  | .triv => True
  | .type1 _ Q₁ Q₂ Q₃ => DominantSrc Q₁ ∧ DominantSrc Q₂ ∧ DominantSrc Q₃
  | .type2 Xp Xm Qlp =>
    PartitionDominant (chainPartition Xp 0) ∧ PartitionDominant (chainPartition Xm 0) ∧
      CouplesDominant Xp ∧ CouplesDominant Xm ∧ DominantSrc Qlp

/-- Every couple `𝒬_{j,ε,ι}` replacing a leaf pair of the chain is dominant. -/
def CouplesDominant : RegChain → Prop
  | .nil => True
  | .pair _ Qr Qg inner rest =>
    DominantSrc Qr ∧ DominantSrc Qg ∧ CouplesDominant inner ∧ CouplesDominant rest
end

mutual
/-- **The B2 draft's `RegCpl.dominant` is DH21 Def 4.17.** -/
theorem dominant_iff_source : (Q : RegCpl) → (Q.dominant = true ↔ DominantSrc Q)
  | .triv => by simp [RegCpl.dominant, DominantSrc]
  | .type1 _ Q₁ Q₂ Q₃ => by
    simp only [RegCpl.dominant, Bool.and_eq_true, DominantSrc, dominant_iff_source Q₁,
      dominant_iff_source Q₂, dominant_iff_source Q₃, and_assoc]
  | .type2 Xp Xm Qlp => by
    simp only [RegCpl.dominant, Bool.and_eq_true, DominantSrc, chain_dominant_iff_source Xp,
      chain_dominant_iff_source Xm, dominant_iff_source Qlp, partition_dominant_iff]
    tauto

/-- A chain code is dominant (draft) iff its partition is dominant and its couples are dominant. -/
theorem chain_dominant_iff_source : (X : RegChain) →
    (X.dominant = true ↔ spineDominant X = true ∧ CouplesDominant X)
  | .nil => by simp [RegChain.dominant, spineDominant, CouplesDominant]
  | .pair m Qr Qg inner rest => by
    have hr := chain_dominant_iff_source rest
    simp only [RegChain.dominant, Bool.and_eq_true, spineDominant, CouplesDominant,
      dominant_iff_source Qr, dominant_iff_source Qg, hr]
    constructor
    · rintro ⟨⟨⟨hn, h1⟩, h2⟩, h3, h4⟩
      have hin : inner = .nil := by cases inner <;> simp_all [RegChain.isNil]
      subst hin
      exact ⟨⟨hn, h3⟩, h1, h2, trivial, h4⟩
    · rintro ⟨⟨hn, h3⟩, h1, h2, -, h4⟩
      exact ⟨⟨⟨hn, h1⟩, h2⟩, h3, h4⟩
end

end WaveTurbulence.Links
