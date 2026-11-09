/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceGroup
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceTop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Collection
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceVC`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a): the units of a VC group

TARGET L1934-L1937 (`defcong`): for a VC `S` of `𝒞`, the vines of `𝒱` among its ingredients are all (CL)
ingredients (`S` not a root block), resp. all but the (CN) ingredient, resp. all but the top vine (root block).
`vc_group`: the spine `L` of `S`, and either the whole `S` is one (CL) block of non-(CN) ingredients all in `𝒱`
(no skipped vine) or `L = LL ++ (A,x,y) :: RR` with the two runs (CL) blocks, every other ingredient in `𝒱`,
and the skipped ingredient (CN), or the top (CL) ingredient of a root VC without (CN) ingredient.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1

variable {w : ℕ} {G : Garden w}

/-- A (CL) vine from a non-(CN) member. -/
theorem exists_clVine {T : Finset (GBranch G.tree)} {p q : GBranch G.tree}
    (h : Src.IsSomeVine Src.γL G.molecule T p q) (hn : ¬ CNMem G (T, p, q)) :
    ∃ c : CLVine G, c.atoms = T ∧ (c.upper = p ∧ c.lower = q ∨ c.upper = q ∧ c.lower = p) := by
  rcases vine_cl_or_cn h with h1 | h1 | h1
  · exact ⟨⟨T, p, q, h, h1.1, h1.2⟩, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨⟨T, q, p, isSomeVine_swap h, h1.1, h1.2⟩, rfl, Or.inr ⟨rfl, rfl⟩⟩
  · exact absurd h1 hn

/-- Two distinct top ingredients cannot exist. -/
theorem top_unique {S : Finset (GBranch G.tree)} {c1 c2 : CLVine G}
    (h1 : IsTopIngredient S c1) (h2 : IsTopIngredient S c2)
    (hi1 : IsIngredient G.molecule S c1.atoms) (hi2 : IsIngredient G.molecule S c2.atoms)
    (hne : c1.atoms ≠ c2.atoms) : False := by
  obtain ⟨hne1, hd1⟩ := h1 c2 hi2 (Ne.symm hne)
  obtain ⟨_, hd2⟩ := h2 c1 hi1 hne
  apply hne1
  obtain ⟨e1, p1⟩ := hd1
  obtain ⟨_, p2⟩ := hd2
  have hp : c1.upper.1.2 = c2.upper.1.2 := List.IsPrefix.eq_of_length_le p1 (List.IsPrefix.length_le p2)
  exact Subtype.ext (Prod.ext e1 hp)

/-- A non-(CN) ingredient of a VC group lies in `𝒱` under the (CL)/(CN)/top conditions of `defcong`. -/
theorem member_mem_vinesV {S : Finset (GBranch G.tree)} (hSmax : S ∈ maximalGroups G.molecule)
    (hVC : ∃ a b, Src.IsVC Src.γL G.molecule S a b) {a b : GBranch G.tree}
    (hB : G.molecule.IsBlock S a b) {n : ℕ} {T : Finset (GBranch G.tree)} {p q : GBranch G.tree}
    (hI : ChainIngredient G.molecule S a b n T p q) (hnon : ¬ CNMem G (T, p, q))
    (hcond : ¬ IsRootVC G S ∨ (IsRootVC G S ∧ ((∃ T', IsIngredient G.molecule S T' ∧ IsCNVine G T') ∨
      ∀ c : CLVine G, c.atoms = T → ¬ IsTopIngredient S c))) :
    ∃ c ∈ vinesV G, c.atoms = T ∧ IsIngredient G.molecule S T := by
  have hvine : Src.IsSomeVine Src.γL G.molecule T p q := (chainIngredient_spec hI).2.1
  obtain ⟨c, hc1, _⟩ := exists_clVine hvine hnon
  have hingr : IsIngredient G.molecule S T := Or.inl ⟨a, b, n, p, q, hB, hI⟩
  refine ⟨c, ⟨S, hSmax, hc1 ▸ hingr, ?_⟩, hc1, hingr⟩
  obtain ⟨a', b', hv⟩ := hVC
  rcases hcond with h | ⟨hroot, hx⟩
  · exact Or.inl ⟨a', b', hv, h⟩
  · refine Or.inr ⟨Or.inr hroot, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hx c hc1)

theorem RunCut.atoms_ne {D' : Type*} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} {A : Finset (GBranch G.tree)} {x y : GBranch G.tree}
    (rc : RunCut G N L S a b A x y) (hxy : x ∈ A ∧ y ∈ A ∧ x ≠ y)
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ L) (hne : t ≠ (A, x, y)) :
    t.1 ≠ A := by
  intro hA
  have hAne : ∀ {Z : Finset (GBranch G.tree)} {z : GBranch G.tree}, A ⊆ Z → Z ∩ A = {z} → False := by
    intro Z z hAZ hZA
    have h1 : x ∈ Z ∩ A := mem_inter.mpr ⟨hAZ hxy.1, hxy.1⟩
    have h2 : y ∈ Z ∩ A := mem_inter.mpr ⟨hAZ hxy.2.1, hxy.2.1⟩
    rw [hZA, mem_singleton] at h1 h2
    exact hxy.2.2 (h1.trans h2.symm)
  rw [rc.hL] at ht
  rcases List.mem_append.mp ht with h | h
  · rcases rc.left with ⟨h0, _⟩ | ⟨_, _, hLL, hLA⟩
    · rw [h0] at h; simp at h
    · exact hAne (hA ▸ (hLL.mem_vine (T := t.1) (p := t.2.1) (q := t.2.2) h).2) hLA
  · rcases List.mem_cons.mp h with h | h
    · exact hne h
    · rcases rc.right with ⟨h0, _⟩ | ⟨_, _, hRR, hRA⟩
      · rw [h0] at h; simp at h
      · exact hAne (hA ▸ (hRR.mem_vine (T := t.1) (p := t.2.1) (q := t.2.2) h).2) hRA

/-- The specification of the units of a VC group. -/
@[expose] def VCSplitSpec (G : Garden w) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree)
    (L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)) : Prop :=
  ((∀ t ∈ L, ¬ CNMem G t) ∧
    (∃ u : CLBlock G, u.atoms = S ∧ (u.upper = a ∧ u.lower = b ∨ u.upper = b ∧ u.lower = a) ∧
      7 ≤ G.molecule.deg u.upper + G.molecule.deg u.lower) ∧
    (∀ t ∈ L, ∃ c ∈ vinesV G, c.atoms = t.1 ∧ IsIngredient G.molecule S t.1)) ∨
  (∃ (A : Finset (GBranch G.tree)) (x y : GBranch G.tree), (A, x, y) ∈ L ∧
    Src.IsSomeVine Src.γL G.molecule A x y ∧ IsIngredient G.molecule S A ∧ G.molecule.IsBlock S a b ∧
    Nonempty (RunCut G G.molecule L S a b A x y) ∧
    (∀ t ∈ L, t ≠ (A, x, y) → ∃ c ∈ vinesV G, c.atoms = t.1 ∧ IsIngredient G.molecule S t.1) ∧
    (CNMem G (A, x, y) ∨ (IsRootVC G S ∧ (∀ t ∈ L, ¬ CNMem G t) ∧
      ∃ c : CLVine G, c.atoms = A ∧ IsTopIngredient S c)))

/-- **The units of a VC group** (TARGET L1934-L1937). -/
theorem vc_group (hM : G.molecule.IsMolecule) {S : Finset (GBranch G.tree)}
    (hSmax : S ∈ maximalGroups G.molecule) {a b : GBranch G.tree}
    (hvc : Src.IsVC Src.γL G.molecule S a b) :
    ∃ L, ∃ _ : Spine G.molecule L S a b, VCSplitSpec G S a b L := by
  obtain ⟨hB, n, hn⟩ := hvc
  obtain ⟨L, hs⟩ := Spine.of_chain hn
  refine ⟨L, hs, ?_⟩
  have hVC : ∃ a b, Src.IsVC Src.γL G.molecule S a b := ⟨a, b, hB, n, hn⟩
  have hblk : ∀ T p q, (T, p, q) ∈ L → G.molecule.IsBlock T p q :=
    fun T p q hm => (hs.mem_vine hm).1.block
  have hing : ∀ T p q, (T, p, q) ∈ L → ChainIngredient G.molecule S a b L.length T p q :=
    fun T p q hm => hs.ingredient_of_mem hm
  have hisI : ∀ T p q, (T, p, q) ∈ L → IsIngredient G.molecule S T :=
    fun T p q hm => Or.inl ⟨a, b, L.length, p, q, hB, hing T p q hm⟩
  by_cases hcn : ∃ t ∈ L, CNMem G t
  · obtain ⟨⟨A, x, y⟩, hmem, hc⟩ := hcn
    have hnon : ∀ t ∈ L, t ≠ (A, x, y) → ¬ CNMem G t := fun t ht hne hct =>
      hne (hs.cn_unique hblk ht hmem hct hc)
    obtain ⟨rc⟩ := group_split hM hs hB (fun X x y _ _ h => h) hmem hnon
    refine Or.inr ⟨A, x, y, hmem, (hs.mem_vine hmem).1, hisI A x y hmem, hB, ⟨rc⟩, ?_, Or.inl hc⟩
    intro t ht hne
    obtain ⟨T, p, q⟩ := t
    refine member_mem_vinesV hSmax hVC hB (hing T p q ht) (hnon _ ht hne) ?_
    by_cases hroot : IsRootVC G S
    · exact Or.inr ⟨hroot, Or.inl ⟨A, hisI A x y hmem, x, y, (hs.mem_vine hmem).1, hc.1, hc.2⟩⟩
    · exact Or.inl hroot
  · have hnon : ∀ t ∈ L, ¬ CNMem G t := fun t ht hct => hcn ⟨t, ht, hct⟩
    by_cases htop : IsRootVC G S ∧ ∃ t ∈ L, ∃ c : CLVine G, c.atoms = t.1 ∧ IsTopIngredient S c
    · obtain ⟨hroot, ⟨A, x, y⟩, hmem, c0, hc0, hc0top⟩ := htop
      obtain ⟨rc⟩ := group_split hM hs hB (fun X x y _ _ h => h) hmem (fun t ht _ => hnon t ht)
      refine Or.inr ⟨A, x, y, hmem, (hs.mem_vine hmem).1, hisI A x y hmem, hB, ⟨rc⟩, ?_, Or.inr ⟨hroot, hnon, c0, hc0, hc0top⟩⟩
      intro t ht hne
      obtain ⟨T, p, q⟩ := t
      refine member_mem_vinesV hSmax hVC hB (hing T p q ht) (hnon _ ht) (Or.inr ⟨hroot, Or.inr ?_⟩)
      intro c hc hctop
      have hxy := isSomeVine_ends_RedSpliceSplit (hs.mem_vine hmem).1
      have hAT : T ≠ A := rc.atoms_ne hxy ht hne
      have hc0' : c0.atoms = A := hc0
      refine top_unique hctop hc0top (hc ▸ hisI T p q ht) (hc0' ▸ hisI A x y hmem) ?_
      rw [hc, hc0']
      exact hAT
    · refine Or.inl ⟨hnon, ?_, ?_⟩
      · obtain ⟨u, hu1, hu2⟩ := Spine.clBlock hs hnon hB
        refine ⟨u, hu1, hu2, ?_⟩
        by_contra hlt
        push Not at hlt
        have hrootS : IsRootVC G S := by
          refine ⟨a, b, ⟨hB, n, hn⟩, ?_, ?_⟩
          · rcases hu2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have := hu1 ▸ u.cl
              rw [h1, h2] at this
              exact Or.inl this
            · have := hu1 ▸ u.cl
              rw [h1, h2] at this
              exact Or.inr this
          · rcases hu2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2] at hlt; omega
            · rw [h1, h2] at hlt; omega
        exact htop ⟨hrootS, vc_top_exists hM hs hB hnon hrootS⟩
      · intro t ht
        obtain ⟨T, p, q⟩ := t
        refine member_mem_vinesV hSmax hVC hB (hing T p q ht) (hnon _ ht) ?_
        by_cases hroot : IsRootVC G S
        · refine Or.inr ⟨hroot, Or.inr ?_⟩
          intro c hc hctop
          exact htop ⟨hroot, _, ht, c, hc, hctop⟩
        · exact Or.inl hroot

end WaveTurbulence.GammaLow.FinalCount.H
