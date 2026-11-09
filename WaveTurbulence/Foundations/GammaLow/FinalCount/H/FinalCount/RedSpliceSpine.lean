/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSpine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceSplit
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.RS.Facts
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceSpine`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a): spines (ordered ingredient lists) of vine chains

A `Spine M L U a b` is an ordered list `L` of vines `(T, p, q)` forming the vine chain `U` from `a` to `b`
(consecutive vines share exactly their joint).  `Chain` and `ChainIngredient` are the unordered forms; the
spine is the derivation.  Main facts: the ingredients of a chain are the members of any of its spines
(`ingredient_iff_mem`), the spine of a block chain is unique (`Spine.unique`, by the terminal split of a vine
inside a block), and spines concatenate (`Spine.append_spine`).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- An ordered chain of vines `(T, p, q)`: `p`, `q` the left and right joint of the ingredient. -/
inductive Spine (M : Molecule V D) : List (Finset V × V × V) → Finset V → V → V → Prop
  | one {T a b} : Src.IsSomeVine Src.γL M T a b → Spine M [(T, a, b)] T a b
  | snoc {L U T a b c} : Spine M L U a b → Src.IsSomeVine Src.γL M T b c → U ∩ T = {b} → a ≠ c →
      Spine M (L ++ [(T, b, c)]) (U ∪ T) a c

namespace Spine
open Spine

theorem chain {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine M L U a b) :
    Src.Chain Src.γL M U a b L.length := by
  induction h with
  | one hv => exact Src.Chain.single hv
  | snoc _ hT hi hne ih =>
    rw [List.length_append]
    exact Src.Chain.append ih hT hi hne

theorem of_chain {U : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M U a b n) :
    ∃ L, Spine M L U a b := by
  induction h with
  | single hv => exact ⟨_, Spine.one hv⟩
  | append _ hT hi hne ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨_, Spine.snoc hL hT hi hne⟩

theorem ends {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine M L U a b) :
    a ∈ U ∧ b ∈ U ∧ a ≠ b := chain_ends' h.chain

theorem mem_vine {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine M L U a b)
    {T : Finset V} {p q : V} (hm : (T, p, q) ∈ L) : Src.IsSomeVine Src.γL M T p q ∧ T ⊆ U := by
  induction h with
  | one hv =>
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ⟨hv, Finset.Subset.refl _⟩
  | snoc _ hT _ _ ih =>
    rcases List.mem_append.mp hm with h1 | h1
    · obtain ⟨h2, h3⟩ := ih h1
      exact ⟨h2, h3.trans subset_union_left⟩
    · simp only [List.mem_singleton, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ⟨hT, subset_union_right⟩

theorem ingredient_of_mem {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine M L U a b)
    {T : Finset V} {p q : V} (hm : (T, p, q) ∈ L) : ChainIngredient M U a b L.length T p q := by
  induction h with
  | one hv =>
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact ChainIngredient.single hv
  | snoc hS hT hi hne ih =>
    rw [List.length_append]
    rcases List.mem_append.mp hm with h1 | h1
    · exact ChainIngredient.append_left (ih h1) hT hi hne
    · simp only [List.mem_singleton, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      exact ChainIngredient.append_last hS.chain hT hi hne

theorem mem_of_ingredient {U A : Finset V} {a b x y : V} {n : ℕ} (h : ChainIngredient M U a b n A x y) :
    ∃ L, Spine M L U a b ∧ (A, x, y) ∈ L := by
  induction h with
  | single hv => exact ⟨_, Spine.one hv, by simp⟩
  | append_left _ hT hi hne ih =>
    obtain ⟨L, hL, hm⟩ := ih
    exact ⟨_, Spine.snoc hL hT hi hne, List.mem_append_left _ hm⟩
  | append_last hS hT hi hne =>
    obtain ⟨L, hL⟩ := of_chain hS
    exact ⟨_, Spine.snoc hL hT hi hne, by simp⟩

/-- Concatenation of spines meeting in the common joint. -/
theorem append_spine {L1 L2 : List (Finset V × V × V)} {U1 U2 : Finset V} {a x b : V}
    (h1 : Spine M L1 U1 a x) (h2 : Spine M L2 U2 x b) (hi : U1 ∩ U2 = {x}) (hne : a ≠ b) :
    Spine M (L1 ++ L2) (U1 ∪ U2) a b := by
  induction h2 with
  | @one T x' b' hv =>
    exact Spine.snoc h1 hv hi hne
  | @snoc L2' U2' T x' b' c h2' hT hi2 hne2 ih =>
    have hxU2' : x' ∈ U2' := h2'.ends.1
    have hb'U2' : b' ∈ U2' := h2'.ends.2.1
    have hsub : U1 ∩ U2' ⊆ U1 ∩ (U2' ∪ T) := inter_subset_inter_left subset_union_left
    have hi' : U1 ∩ U2' = {x'} := by
      apply Finset.Subset.antisymm
      · intro v hv
        have := hsub hv
        rw [hi] at this
        exact this
      · intro v hv
        rw [mem_singleton] at hv
        subst hv
        exact mem_inter.mpr ⟨h1.ends.2.1, hxU2'⟩
    have hne' : a ≠ b' := by
      intro hab
      have : a ∈ U1 ∩ U2' := mem_inter.mpr ⟨h1.ends.1, hab ▸ hb'U2'⟩
      rw [hi'] at this
      exact h1.ends.2.2 (mem_singleton.mp this)
    have ih' := ih h1 hi' hne'
    have hTsub : U1 ∩ T ⊆ {x'} := by
      intro v hv
      obtain ⟨hv1, hv2⟩ := mem_inter.mp hv
      have : v ∈ U1 ∩ (U2' ∪ T) := mem_inter.mpr ⟨hv1, mem_union_right _ hv2⟩
      rw [hi] at this
      exact this
    have hi3 : (U1 ∪ U2') ∩ T = {b'} := by
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨hv1, hv2⟩ := mem_inter.mp hv
        rcases mem_union.mp hv1 with hv1 | hv1
        · have := hTsub (mem_inter.mpr ⟨hv1, hv2⟩)
          rw [mem_singleton] at this
          subst this
          have : v ∈ U2' ∩ T := mem_inter.mpr ⟨hxU2', hv2⟩
          rw [hi2] at this
          exact this
        · have : v ∈ U2' ∩ T := mem_inter.mpr ⟨hv1, hv2⟩
          rw [hi2] at this
          exact this
      · intro v hv
        rw [mem_singleton] at hv
        subst hv
        exact mem_inter.mpr ⟨mem_union_right _ hb'U2', (isSomeVine_ends_RedSpliceSplit hT).1⟩
    have := Spine.snoc ih' hT hi3 hne
    rw [← List.append_assoc, ← Finset.union_assoc]
    exact this

/-- A vine cannot be the union of a chain and a last vine. -/
theorem vine_not_snoc (hM : M.IsMolecule) {L : List (Finset V × V × V)} {S T : Finset V} {a b c : V}
    (hS : Spine M L S a b) (hT : Src.IsSomeVine Src.γL M T b c) (hi : S ∩ T = {b})
    (hV : Src.IsSomeVine Src.γL M (S ∪ T) a c) : False := by
  have hX := hV
  have hsplit := RS.vine_in_terminal_split M hM hT.block hX.block hS.ends.2.1 hX (Finset.Subset.refl _)
  have hc : c ∈ S ∪ T := hX.block.2.2.1
  have hcT : c ∈ T := hT.block.2.2.1
  have ha : a ∈ S ∪ T := hX.block.2.1
  rcases hsplit with h | h
  · have hcS : c ∈ S := h hc
    have : c ∈ S ∩ T := mem_inter.mpr ⟨hcS, hcT⟩
    rw [hi] at this
    exact hT.block.2.2.2.1 (mem_singleton.mp this).symm
  · have haT : a ∈ T := h ha
    have : a ∈ S ∩ T := mem_inter.mpr ⟨hS.ends.1, haT⟩
    rw [hi] at this
    exact hS.ends.2.2 (mem_singleton.mp this)

theorem sub_last (hM : M.IsMolecule) {L2 : List (Finset V × V × V)} {S2 T1 T2 : Finset V}
    {a b1 b2 c : V} (hS2 : Spine M L2 S2 a b2) (hi2 : S2 ∩ T2 = {b2})
    (hY1 : Src.IsSomeVine Src.γL M T1 b1 c) (hY2 : Src.IsSomeVine Src.γL M T2 b2 c)
    (hB2 : M.IsBlock (S2 ∪ T2) a c) (hsub : T1 ⊆ S2 ∪ T2) : T1 ⊆ T2 := by
  rcases RS.vine_in_terminal_split M hM hY2.block hB2 hS2.ends.2.1 hY1 hsub with h | h
  · exfalso
    have hc : c ∈ S2 := h hY1.block.2.2.1
    have : c ∈ S2 ∩ T2 := mem_inter.mpr ⟨hc, hY2.block.2.2.1⟩
    rw [hi2] at this
    exact hY2.block.2.2.2.1 (mem_singleton.mp this).symm
  · exact h

theorem last_eq (hM : M.IsMolecule) {L1 L2 : List (Finset V × V × V)} {S1 S2 T1 T2 : Finset V}
    {a b1 b2 c : V} (hS1 : Spine M L1 S1 a b1) (hT1 : Src.IsSomeVine Src.γL M T1 b1 c) (hi1 : S1 ∩ T1 = {b1})
    (hS2 : Spine M L2 S2 a b2) (hT2 : Src.IsSomeVine Src.γL M T2 b2 c) (hi2 : S2 ∩ T2 = {b2})
    (hU : S1 ∪ T1 = S2 ∪ T2) (hB : M.IsBlock (S1 ∪ T1) a c) : T1 = T2 := by
  have hB2 : M.IsBlock (S2 ∪ T2) a c := hU ▸ hB
  apply Finset.Subset.antisymm
  · exact sub_last hM hS2 hi2 hT1 hT2 hB2 (hU ▸ subset_union_right)
  · exact sub_last hM hS1 hi1 hT2 hT1 hB (hU ▸ subset_union_right)

theorem inv {L : List (Finset V × V × V)} {U : Finset V} {a c : V} (h : Spine M L U a c) :
    (∃ T, L = [(T, a, c)] ∧ U = T ∧ Src.IsSomeVine Src.γL M T a c) ∨
    (∃ L' U' T b, L = L' ++ [(T, b, c)] ∧ U = U' ∪ T ∧ Spine M L' U' a b ∧ Src.IsSomeVine Src.γL M T b c ∧
      U' ∩ T = {b} ∧ a ≠ c) := by
  cases h with
  | one hv => exact Or.inl ⟨_, rfl, rfl, hv⟩
  | snoc h hT hi hne => exact Or.inr ⟨_, _, _, _, rfl, rfl, h, hT, hi, hne⟩

/-- **The spine of a block chain is unique.** -/
theorem unique (hM : M.IsMolecule) {L1 L2 : List (Finset V × V × V)} {U : Finset V} {a c : V}
    (h1 : Spine M L1 U a c) (h2 : Spine M L2 U a c) (hB : M.IsBlock U a c) : L1 = L2 := by
  induction h1 generalizing L2 with
  | @one T a c hv =>
    rcases h2.inv with ⟨T', rfl, hT, _⟩ | ⟨L', U', T', b, rfl, hU, hS, hT, hi, hne⟩
    · rw [← hT]
    · rw [hU] at hv
      exact (vine_not_snoc hM hS hT hi hv).elim
  | @snoc L1' U1' T1 a b1 c h1' hT1 hi1 hne1 ih =>
    rcases h2.inv with ⟨T', rfl, hT, hv⟩ | ⟨L2', U2', T2, b2, rfl, hU, h2', hT2, hi2, hne2⟩
    · rw [← hT] at hv
      exact (vine_not_snoc hM h1' hT1 hi1 hv).elim
    · have hTT := last_eq hM h1' hT1 hi1 h2' hT2 hi2 hU hB
      subst hTT
      have hbb : b1 = b2 := by
        have := Vine.block_joints_unique M hT1.block hT2.block
        rcases Mole.finset_pair_eq_pair_iff.mp this with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hT1.block.2.2.2.1
      subst hbb
      have hUU := inter_eq_of_union hU hi1 hi2 h1'.ends.2.1 h2'.ends.2.1
      subst hUU
      have hB' := RS.chain_prefix_isBlock M hM h1'.chain hT1 hi1 hB
      rw [ih h2' hB']

end Spine

end WaveTurbulence.GammaLow.FinalCount.H
