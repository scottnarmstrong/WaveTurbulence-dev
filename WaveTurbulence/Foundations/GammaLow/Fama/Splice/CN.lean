/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceCN` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.Molecule.BlockChains
public import WaveTurbulence.Foundations.Spine.SourceJointPairDichotomy
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceCN


/-!
# REDSPLICE-DEF (S2a): at most one (CN) ingredient in a spine

TARGET `blockchainprop` (DH23 Cor 4.13), for the spines of `RedSpliceSpine`: along a vine chain in a garden
molecule, the parent pattern of the ingredients is `down* [CN] up*`; hence at most one ingredient is (CN), and
a (CN) ingredient forces the right joint parent of the last ingredient outside.  (`Mole.chain_at_most_one_cn`
is the same statement for lists of `GardenBlockSegment`; here it is proved directly on spines, which avoids
the bridge to lists.)
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree

variable {w : ℕ} {G : Garden w} {γ : ℝ}

theorem Spine.last {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {L : List (Finset V × V × V)} {U : Finset V} {a b : V} (h : Spine γ M L U a b) :
    ∃ L0 A p, L = L0 ++ [(A, p, b)] := by
  rcases h.inv with ⟨T, rfl, _⟩ | ⟨L', U', T, b', rfl, _⟩
  · exact ⟨[], T, a, rfl⟩
  · exact ⟨L', T, b', rfl⟩

/-- The block-pattern trichotomy for a vine of the garden molecule. -/
theorem vine_cl_or_cn {T : Finset (GBranch G.tree)} {p q : GBranch G.tree}
    (h : Src.IsSomeVine γ G.molecule T p q) :
    CLParentPattern G T p q ∨ CLParentPattern G T q p ∨ CNParentPattern G T p q :=
  block_parent_patterns G (Src.isBlock_of_isSomeVine h)

theorem Spine.cn_clause {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hs : Spine γ N L U a b)
    (hblk : ∀ T p q, (T, p, q) ∈ L → G.molecule.IsBlock T p q) :
    (∀ t1 ∈ L, ∀ t2 ∈ L, CNMem G t1 → CNMem G t2 → t1 = t2) ∧
    ∀ L0 A p, L = L0 ++ [(A, p, b)] → (∃ t ∈ L, CNMem G t) → ¬ InternalParent G A b := by
  induction hs with
  | @one T a b hv =>
    refine ⟨?_, ?_⟩
    · intro t1 h1 t2 h2 _ _
      simp only [List.mem_singleton] at h1 h2
      rw [h1, h2]
    · intro L0 A p hL ⟨t, ht, hcn⟩
      simp only [List.mem_singleton] at ht
      subst ht
      have h2 := lastEq (L0 := []) (L1 := L0) (x := (T, a, b)) (y := (A, p, b)) (by rw [List.nil_append]; exact hL)
      simp only [Prod.mk.injEq] at h2
      rw [← h2.1]
      exact hcn.2
  | @snoc L U T a b c hS hT hi hne ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun T' p q hm => hblk T' p q (List.mem_append_left _ hm))
    obtain ⟨L0, A0, p0, hL⟩ := hS.last
    have hmem : (A0, p0, b) ∈ L := by rw [hL]; simp
    obtain ⟨hA0, hA0U⟩ := hS.mem_vine hmem
    have hbl0 : G.molecule.IsBlock A0 p0 b := hblk A0 p0 b (List.mem_append_left _ hmem)
    have hblT : G.molecule.IsBlock T b c := hblk T b c (by simp)
    have hbA0 : b ∈ A0 := (isSomeVine_ends hA0).2.1
    have hbT : b ∈ T := (isSomeVine_ends hT).1
    have hf : SegmentFollows G (segOfBlock hbl0) (segOfBlock hblT) := by
      refine ⟨rfl, ?_⟩
      show A0 ∩ T = {b}
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨h1, h2⟩ := mem_inter.mp hv
        have : v ∈ U ∩ T := mem_inter.mpr ⟨hA0U h1, h2⟩
        rw [hi] at this
        exact this
      · intro v hv
        rw [mem_singleton] at hv
        subst hv
        exact mem_inter.mpr ⟨hbA0, hbT⟩
    have hsh : InternalParent G A0 b ∨ InternalParent G T b := segment_shared_parent G hf
    have hexcl : InternalParent G T b → ¬ InternalParent G T c :=
      segment_parent_exclusion G (segOfBlock hblT)
    by_cases hex : ∃ t ∈ L, CNMem G t
    · have hnA : ¬ InternalParent G A0 b := ih2 L0 A0 p0 hL hex
      have hTb : InternalParent G T b := hsh.resolve_left hnA
      have hTnot : ¬ CNMem G (T, b, c) := fun h => h.1 hTb
      refine ⟨?_, ?_⟩
      · intro t1 h1 t2 h2 c1 c2
        rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
        · exact ih1 t1 h1 t2 h2 c1 c2
        · simp only [List.mem_singleton] at h2; subst h2; exact absurd c2 hTnot
        · simp only [List.mem_singleton] at h1; subst h1; exact absurd c1 hTnot
        · simp only [List.mem_singleton] at h1 h2; rw [h1, h2]
      · intro L1 A p hL1 _
        have h2 := lastEq hL1.symm
        simp only [Prod.mk.injEq] at h2
        rw [h2.1]
        exact hexcl hTb
    · have hnoCN : ∀ t ∈ L, ¬ CNMem G t := fun t ht hc => hex ⟨t, ht, hc⟩
      refine ⟨?_, ?_⟩
      · intro t1 h1 t2 h2 c1 c2
        rcases List.mem_append.mp h1 with h1 | h1
        · exact absurd c1 (hnoCN t1 h1)
        rcases List.mem_append.mp h2 with h2 | h2
        · exact absurd c2 (hnoCN t2 h2)
        simp only [List.mem_singleton] at h1 h2; rw [h1, h2]
      · intro L1 A p hL1 ⟨t, ht, hct⟩
        have h2 := lastEq hL1.symm
        simp only [Prod.mk.injEq] at h2
        rw [h2.1]
        rcases List.mem_append.mp ht with ht | ht
        · exact absurd hct (hnoCN t ht)
        · simp only [List.mem_singleton] at ht; subst ht; exact hct.2

/-- **At most one (CN) ingredient**: two (CN) members of one spine coincide. -/
theorem Spine.cn_unique {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hs : Spine γ N L U a b)
    (hblk : ∀ T p q, (T, p, q) ∈ L → G.molecule.IsBlock T p q) {t1 t2 : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (h1 : t1 ∈ L) (h2 : t2 ∈ L) (c1 : CNMem G t1) (c2 : CNMem G t2) : t1 = t2 :=
  (hs.cn_clause hblk).1 t1 h1 t2 h2 c1 c2

end WaveTurbulence.GammaLow.Fama
