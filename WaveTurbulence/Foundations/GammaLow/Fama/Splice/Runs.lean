/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceRuns` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceRuns


/-!
# REDSPLICE-DEF (S2a): the runs of a spine around a skipped ingredient

`Spine.split_around`: a member `(A, x, y)` of the spine `L` of a block chain `S` cuts it into
`L = LL ++ (A,x,y) :: RR`, the spines of two runs `L0`, `R0` (each possibly empty) with
`S = L0 ∪ A ∪ R0`, `L0 ∩ A = {x}`, `R0 ∩ A = {y}`.  `Spine.cl_end_parent`: a spine without (CN) member
carries an internal parent at an end joint; `clBlock_of_spine`: hence it is a (CL) block of the garden.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree

section generic
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {N : Molecule V D} {γ : ℝ} [Fact TVineF1Input]

theorem Spine.split_around (hN : N.IsMolecule) {L : List (Finset V × V × V)} {S : Finset V} {a b : V}
    (hs : Spine γ N L S a b) (hB : N.IsBlock S a b) {A : Finset V} {x y : V} (hA : (A, x, y) ∈ L) :
    ∃ (LL RR : List (Finset V × V × V)) (L0 R0 : Finset V), L = LL ++ (A, x, y) :: RR ∧ S = L0 ∪ A ∪ R0 ∧
      (LL = [] ∧ L0 = ∅ ∧ x = a ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ Spine γ N LL L0 a x ∧ L0 ∩ A = {x})) ∧
      (RR = [] ∧ R0 = ∅ ∧ y = b ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ Spine γ N RR R0 y b ∧ R0 ∩ A = {y})) ∧
      Disjoint L0 R0 := by
  have hI := hs.ingredient_of_mem hA
  obtain ⟨L0, R0, hS, hL, hR, hd⟩ := ingredient_runs hN hI hB
  obtain ⟨hAv, hAS⟩ := hs.mem_vine hA
  -- spines of the two runs
  have hLsp : (L0 = ∅ ∧ x = a) ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ L0 ∩ A = {x} ∧ ∃ LL, Spine γ N LL L0 a x) := by
    rcases hL with h | ⟨h1, h2, ⟨m, hm⟩, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h4, Spine.of_chain hm⟩
  have hRsp : (R0 = ∅ ∧ y = b) ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ R0 ∩ A = {y} ∧ ∃ RR, Spine γ N RR R0 y b) := by
    rcases hR with h | ⟨h1, h2, ⟨m, hm⟩, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h4, Spine.of_chain hm⟩
  have hxy := isSomeVine_ends hAv
  -- the glued spine
  have key : ∃ (LL RR : List (Finset V × V × V)),
      Spine γ N (LL ++ (A, x, y) :: RR) (L0 ∪ A ∪ R0) a b ∧
      (LL = [] ∧ L0 = ∅ ∧ x = a ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ Spine γ N LL L0 a x ∧ L0 ∩ A = {x})) ∧
      (RR = [] ∧ R0 = ∅ ∧ y = b ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ Spine γ N RR R0 y b ∧ R0 ∩ A = {y})) := by
    rcases hLsp with ⟨rfl, rfl⟩ | ⟨hxa, hLB, hLA, LL, hLL⟩
    · rcases hRsp with ⟨rfl, rfl⟩ | ⟨hyb, hRB, hRA, RR, hRR⟩
      · refine ⟨[], [], ?_, Or.inl ⟨rfl, rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
        simp only [Finset.empty_union, Finset.union_empty, List.nil_append]
        exact Spine.one hAv
      · have hsp := Spine.append_spine (Spine.one hAv) hRR (by
          rw [Finset.inter_comm]; exact hRA) hs.ends.2.2
        refine ⟨[], RR, ?_, Or.inl ⟨rfl, rfl, rfl⟩, Or.inr ⟨hyb, hRB, hRR, hRA⟩⟩
        simpa only [Finset.empty_union, List.nil_append, List.singleton_append] using hsp
    · have hLA' := Spine.snoc hLL hAv hLA (by
        intro hay
        have : a ∈ L0 ∩ A := mem_inter.mpr ⟨hLL.ends.1, hay ▸ hxy.2.1⟩
        rw [hLA] at this
        exact hxa (mem_singleton.mp this).symm)
      rcases hRsp with ⟨rfl, rfl⟩ | ⟨hyb, hRB, hRA, RR, hRR⟩
      · refine ⟨LL, [], ?_, Or.inr ⟨hxa, hLB, hLL, hLA⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
        simpa only [Finset.union_empty, List.append_nil, List.cons_append, List.nil_append] using hLA'
      · have hi : (L0 ∪ A) ∩ R0 = {y} := by
          rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.empty_union,
            Finset.inter_comm, hRA]
        have hsp := Spine.append_spine hLA' hRR hi hs.ends.2.2
        refine ⟨LL, RR, ?_, Or.inr ⟨hxa, hLB, hLL, hLA⟩, Or.inr ⟨hyb, hRB, hRR, hRA⟩⟩
        simpa only [List.append_assoc, List.singleton_append] using hsp
  obtain ⟨LL, RR, hsp, hLo, hRo⟩ := key
  rw [← hS] at hsp
  have huniq := Spine.unique hN hs hsp hB
  exact ⟨LL, RR, L0, R0, huniq, hS, hLo, hRo, hd⟩

end generic

section garden
variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input]

/-- A spine without (CN) member carries an internal parent at an end joint. -/
theorem Spine.cl_end_parent {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hs : Spine γ N L U a b)
    (hnon : ∀ t ∈ L, ¬ CNMem G t) : InternalParent G U a ∨ InternalParent G U b := by
  induction hs with
  | @one T a b hv =>
    have := hnon (T, a, b) (by simp)
    unfold CNMem at this
    by_contra hc
    push Not at hc
    exact this ⟨fun h => hc.1 (by simpa using h), fun h => hc.2 (by simpa using h)⟩
  | @snoc L U T a b c hS hT hi hne ih =>
    have ih' := ih (fun t ht => hnon t (List.mem_append_left _ ht))
    have hn := hnon (T, b, c) (by simp)
    unfold CNMem at hn
    have hT' : InternalParent G T b ∨ InternalParent G T c := by
      by_contra hc
      push Not at hc
      exact hn ⟨hc.1, hc.2⟩
    rcases ih' with h | h
    · exact Or.inl (internalParent_mono subset_union_left h)
    · rcases hT' with h' | h'
      · exact absurd (not_internalParent_of_inter hi h h') id
      · exact Or.inr (internalParent_mono subset_union_right h')

/-- A spine of members without (CN) whose union is a block of the garden molecule is a (CL) block. -/
theorem Spine.clBlock {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hs : Spine γ N L U a b)
    (hnon : ∀ t ∈ L, ¬ CNMem G t) (hB : G.molecule.IsBlock U a b) :
    ∃ u : CLBlock G, u.atoms = U ∧ (u.upper = a ∧ u.lower = b ∨ u.upper = b ∧ u.lower = a) := by
  have hep := hs.cl_end_parent hnon
  have hpat : CLParentPattern G U a b ∨ CLParentPattern G U b a := by
    rcases block_parent_patterns G hB with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases hep with h' | h'
      · exact h.1 h'
      · exact h.2 h'
  by_cases h : CLParentPattern G U a b
  · exact ⟨⟨U, a, b, hB, h⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨⟨U, b, a, block_swap_joints G.molecule hB, hpat.resolve_left h⟩, rfl, Or.inr ⟨rfl, rfl⟩⟩

end garden

end WaveTurbulence.GammaLow.Fama
