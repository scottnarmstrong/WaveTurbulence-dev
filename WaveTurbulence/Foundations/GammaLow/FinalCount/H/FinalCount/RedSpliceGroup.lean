/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGroup
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceRuns
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceGroup`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a): the (CL) runs of a group around its skipped ingredient

`group_split`: let `L` be a spine of the group `S` (in a molecule `N`: the garden molecule for a VC, the adjoint
for an HVC), `(A, x, y)` a member such that every other member is non-(CN).  Then
`L = LL ++ (A,x,y) :: RR`, `S = L0 ∪ A ∪ R0`, and the two runs `L0`, `R0` are empty or (CL) blocks of the garden
(`CLBlock`) with joints `a, x` and `y, b`; `L0 ∩ A = {x}`, `R0 ∩ A = {y}`, `L0`, `R0` disjoint.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree

variable {w : ℕ} {G : Garden w} {D' : Type*} [Fintype D'] [DecidableEq D']

/-- The result of cutting a group around a skipped ingredient. -/
structure RunCut (G : Garden w) (N : Molecule (GBranch G.tree) D')
    (L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree))
    (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) (A : Finset (GBranch G.tree))
    (x y : GBranch G.tree) where
  LL : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)
  RR : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)
  L0 : Finset (GBranch G.tree)
  R0 : Finset (GBranch G.tree)
  hL : L = LL ++ (A, x, y) :: RR
  hS : S = L0 ∪ A ∪ R0
  disj : Disjoint L0 R0
  left : LL = [] ∧ L0 = ∅ ∧ x = a ∨ (x ≠ a ∧ N.IsBlock L0 a x ∧ Spine N LL L0 a x ∧ L0 ∩ A = {x})
  right : RR = [] ∧ R0 = ∅ ∧ y = b ∨ (y ≠ b ∧ N.IsBlock R0 y b ∧ Spine N RR R0 y b ∧ R0 ∩ A = {y})
  leftBlock : L0 = ∅ ∨ ∃ u : CLBlock G, u.atoms = L0 ∧ (u.upper = a ∧ u.lower = x ∨ u.upper = x ∧ u.lower = a)
  rightBlock : R0 = ∅ ∨ ∃ u : CLBlock G, u.atoms = R0 ∧ (u.upper = y ∧ u.lower = b ∨ u.upper = b ∧ u.lower = y)

theorem group_split {N : Molecule (GBranch G.tree) D'} (hN : N.IsMolecule)
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (hs : Spine N L S a b) (hB : N.IsBlock S a b)
    (hrun : ∀ X x y, X ⊆ S → ¬ (a ∈ X ∧ b ∈ X) → N.IsBlock X x y → G.molecule.IsBlock X x y)
    {A : Finset (GBranch G.tree)} {x y : GBranch G.tree} (hA : (A, x, y) ∈ L)
    (hnon : ∀ t ∈ L, t ≠ (A, x, y) → ¬ CNMem G t) : Nonempty (RunCut G N L S a b A x y) := by
  obtain ⟨LL, RR, L0, R0, hL, hS, hl, hr, hd⟩ := hs.split_around hN hB hA
  obtain ⟨hAv, hAS⟩ := hs.mem_vine hA
  have hxy := isSomeVine_ends_RedSpliceSplit hAv
  have hL0S : L0 ⊆ S := by rw [hS]; exact subset_union_left.trans subset_union_left
  have hR0S : R0 ⊆ S := by rw [hS]; exact subset_union_right
  have hbL : b ∈ L0 → False := by
    intro hb
    rcases hr with ⟨_, _, hyb⟩ | ⟨_, _, hRR, _⟩
    · rcases hl with ⟨_, rfl, _⟩ | ⟨_, _, _, hLA⟩
      · simp at hb
      · have : b ∈ L0 ∩ A := mem_inter.mpr ⟨hb, hyb ▸ hxy.2.1⟩
        rw [hLA] at this
        exact hxy.2.2 ((mem_singleton.mp this).symm.trans hyb.symm)
    · exact (Finset.disjoint_left.mp hd hb) hRR.ends.2.1
  have haR : a ∈ R0 → False := by
    intro ha
    rcases hl with ⟨_, _, hxa⟩ | ⟨_, _, hLL, _⟩
    · rcases hr with ⟨_, rfl, _⟩ | ⟨_, _, _, hRA⟩
      · simp at ha
      · have : a ∈ R0 ∩ A := mem_inter.mpr ⟨ha, hxa ▸ hxy.1⟩
        rw [hRA] at this
        exact hxy.2.2 (hxa.trans (mem_singleton.mp this))
    · exact (Finset.disjoint_right.mp hd ha) hLL.ends.1
  have hAne : ∀ {Z : Finset (GBranch G.tree)} {z : GBranch G.tree}, A ⊆ Z → Z ∩ A = {z} → False := by
    intro Z z hAZ hZA
    have h1 : x ∈ Z ∩ A := mem_inter.mpr ⟨hAZ hxy.1, hxy.1⟩
    have h2 : y ∈ Z ∩ A := mem_inter.mpr ⟨hAZ hxy.2.1, hxy.2.1⟩
    rw [hZA, mem_singleton] at h1 h2
    exact hxy.2.2 (h1.trans h2.symm)
  have hmemL : ∀ t ∈ LL ++ RR, t ∈ L := by
    intro t ht
    rw [hL]
    rcases List.mem_append.mp ht with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  refine ⟨⟨LL, RR, L0, R0, hL, hS, hd, hl, hr, ?_, ?_⟩⟩
  · rcases hl with ⟨_, rfl, _⟩ | ⟨hxa, hLB, hLL, hLA⟩
    · exact Or.inl rfl
    · right
      have hn : ∀ t ∈ LL, ¬ CNMem G t := by
        intro t ht
        refine hnon t (hmemL t (List.mem_append_left _ ht)) ?_
        intro heq
        subst heq
        exact hAne (hLL.mem_vine ht).2 hLA
      exact (Spine.clBlock hLL hn (hrun L0 a x hL0S (fun h => hbL h.2) hLB)).imp fun u hu => hu
  · rcases hr with ⟨_, rfl, _⟩ | ⟨hyb, hRB, hRR, hRA⟩
    · exact Or.inl rfl
    · right
      have hn : ∀ t ∈ RR, ¬ CNMem G t := by
        intro t ht
        refine hnon t (hmemL t (List.mem_append_right _ ht)) ?_
        intro heq
        subst heq
        exact hAne (hRR.mem_vine ht).2 hRA
      exact (Spine.clBlock hRR hn (hrun R0 y b hR0S (fun h => haR h.1) hRB)).imp fun u hu => hu

end WaveTurbulence.GammaLow.FinalCount.H
