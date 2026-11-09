/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceGroup
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceHVCTop2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Unique
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Vinechain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.G3GroupIso
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceCover`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a): covering lemmas for `𝒱_0`

* `ingredient_sub`, `group_eq_of_ingredient`: an ingredient lies in its group, and a vine lies in one group of `𝒞`.
* `clvine_upper_eq`: a (CL) vine is determined by its atoms (its upper joint is the one without internal parent).
* `member_in_run`: a member of the spine other than the skipped ingredient lies in a run.
* `atoms_ne_A`: a vine of `𝒱` is never the skipped ingredient (CN case, or top case of a root VC / HVC).
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1

variable {w : ℕ} {G : Garden w}

theorem groups_disjoint' (hM : G.molecule.IsMolecule) :
    (maximalGroups G.molecule).Pairwise (fun S T => Disjoint S T) := by
  have hpart := partition_eq_maximalGroups (stage1Collection_isPartition hM)
  have := (stage1Collection_isPartition hM).2.1
  rwa [hpart] at this

theorem ingredient_sub {S T : Finset (GBranch G.tree)} (h : IsIngredient G.molecule S T) : T ⊆ S := by
  rcases h with ⟨a, b, n, x, y, _, hI⟩ | ⟨a, b, e, n, x, y, _, _, _, hI⟩
  · exact (chainIngredient_spec hI).2.2
  · exact (chainIngredient_spec hI).2.2

theorem ingredient_nonempty {S T : Finset (GBranch G.tree)} (h : IsIngredient G.molecule S T) : T.Nonempty := by
  rcases h with ⟨a, b, n, x, y, _, hI⟩ | ⟨a, b, e, n, x, y, _, _, _, hI⟩
  · exact ⟨x, (isSomeVine_ends_RedSpliceSplit (chainIngredient_spec hI).2.1).1⟩
  · exact ⟨x, (isSomeVine_ends_RedSpliceSplit (chainIngredient_spec hI).2.1).1⟩

theorem group_eq_of_ingredient (hM : G.molecule.IsMolecule) {S S' T : Finset (GBranch G.tree)}
    (hS : S ∈ maximalGroups G.molecule) (hS' : S' ∈ maximalGroups G.molecule)
    (h : IsIngredient G.molecule S T) (h' : IsIngredient G.molecule S' T) : S = S' := by
  by_contra hne
  obtain ⟨z, hz⟩ := ingredient_nonempty h
  exact Finset.disjoint_left.mp (groups_disjoint' hM hS hS' hne) (ingredient_sub h hz) (ingredient_sub h' hz)

/-- A (CL) vine is determined by its atoms: its upper joint. -/
theorem clvine_upper_eq {c c' : CLVine G} (h : c.atoms = c'.atoms) : c.upper = c'.upper := by
  have hX := c.isVine
  have hY := c'.isVine
  rw [h] at hX
  have hj := Vine.block_joints_unique G.molecule hX.block hY.block
  have hnp : ¬ Mole.InternalParent G c.atoms c.upper := c.notParentUpper
  have hnp' : ¬ Mole.InternalParent G c'.atoms c'.upper := c'.notParentUpper
  have hp : Mole.InternalParent G c'.atoms c'.lower := c'.parentLower
  rw [h] at hnp
  rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨e1, _⟩ | ⟨e1, e2⟩
  · exact e1
  · exfalso
    rw [e1] at hnp
    exact hnp hp

/-- A member of a spine other than the skipped ingredient lies in one of the two runs. -/
theorem member_in_run {D' : Type*} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S A : Finset (GBranch G.tree)}
    {a b x y : GBranch G.tree} (rc : RunCut G N L S a b A x y) {T : Finset (GBranch G.tree)} {p q : GBranch G.tree}
    (hm : (T, p, q) ∈ L) (hne : T ≠ A) : T ⊆ rc.L0 ∨ T ⊆ rc.R0 := by
  rw [rc.hL] at hm
  rcases List.mem_append.mp hm with h | h
  · left
    rcases rc.left with ⟨hLL, _⟩ | ⟨_, _, hs, _⟩
    · rw [hLL] at h; simp at h
    · exact (hs.mem_vine h).2
  · rcases List.mem_cons.mp h with h | h
    · exact absurd (by simpa using congrArg Prod.fst h) hne
    · right
      rcases rc.right with ⟨hRR, _⟩ | ⟨_, _, hs, _⟩
      · rw [hRR] at h; simp at h
      · exact (hs.mem_vine h).2

/-- A vine of `𝒱` is never the skipped ingredient of its group. -/
theorem atoms_ne_A (hM : G.molecule.IsMolecule) {S A : Finset (GBranch G.tree)} {x y : GBranch G.tree}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    (hSmax : S ∈ maximalGroups G.molecule)
    (hmemb : ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L)
    (hVineM : ∀ T p q, (T, p, q) ∈ L → Src.IsSomeVine Src.γL G.molecule T p q)
    (hAv : Src.IsSomeVine Src.γL G.molecule A x y)
    (hkind : CNMem G (A, x, y) ∨ ((∀ t ∈ L, ¬ CNMem G t) ∧
      (IsRootVC G S ∨ ∃ a b, Src.IsHVC Src.γL G.molecule S a b) ∧
      ∃ c0 : CLVine G, c0.atoms = A ∧ IsTopIngredient S c0))
    {c : CLVine G} (hc : c ∈ vinesV G) (hci : IsIngredient G.molecule S c.atoms) : c.atoms ≠ A := by
  intro hcA
  rcases hkind with hcn | ⟨hnon, hgroup, c0, hc0, htop⟩
  · -- the skipped vine is (CN), but `c` is (CL) with the same atoms
    have hX := c.isVine
    have hY := hAv
    rw [hcA] at hX
    have hj := Vine.block_joints_unique G.molecule hX.block hY.block
    have hp : Mole.InternalParent G c.atoms c.lower := c.parentLower
    rw [hcA] at hp
    have hl : c.lower ∈ ({x, y} : Finset (GBranch G.tree)) := by
      rw [← hj]; simp
    rcases mem_insert.mp hl with h | h
    · exact hcn.1 (h ▸ hp)
    · exact hcn.2 ((mem_singleton.mp h) ▸ hp)
  · obtain ⟨S1, hS1, hi1, hcond⟩ := hc
    have hSS : S1 = S := group_eq_of_ingredient hM hS1 hSmax hi1 hci
    subst hSS
    rcases hcond with ⟨a', b', hvc, hnroot⟩ | ⟨_, hcn | hnt⟩
    · rcases hgroup with hroot | ⟨a'', b'', e, he, hBe, _⟩
      · exact hnroot hroot
      · exact vc_not_hyper hvc.1 ⟨e, he, hBe⟩
    · obtain ⟨T, hTi, hTcn⟩ := hcn
      obtain ⟨p, q, hm⟩ := hmemb T hTi
      obtain ⟨a₁, b₁, hTv, h1, h2⟩ := hTcn
      have hX := hTv
      have hY := hVineM T p q hm
      have hj := Vine.block_joints_unique G.molecule hX.block hY.block
      apply hnon (T, p, q) hm
      show ¬ Mole.InternalParent G T p ∧ ¬ Mole.InternalParent G T q
      have hpm : p ∈ ({a₁, b₁} : Finset (GBranch G.tree)) := by rw [hj]; simp
      have hqm : q ∈ ({a₁, b₁} : Finset (GBranch G.tree)) := by rw [hj]; simp
      refine ⟨?_, ?_⟩
      · rcases mem_insert.mp hpm with h | h
        · exact h ▸ h1
        · exact (mem_singleton.mp h) ▸ h2
      · rcases mem_insert.mp hqm with h | h
        · exact h ▸ h1
        · exact (mem_singleton.mp h) ▸ h2
    · apply hnt
      intro c' hI' hne'
      have hup : c.upper = c0.upper := clvine_upper_eq (hcA.trans hc0.symm)
      rw [hup]
      exact htop c' hI' (hc0 ▸ hcA ▸ hne')

end WaveTurbulence.GammaLow.FinalCount.H
