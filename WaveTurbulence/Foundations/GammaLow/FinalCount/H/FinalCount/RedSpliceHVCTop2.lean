/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHVCTop2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceCN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceHVCTop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceRev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.G3GroupIso
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.RedSpliceInduced
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceHVCTop2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a): an HVC group with only (CL) ingredients has a top ingredient

For a spine of (CL) vines the orientations of the members form a word `B...BF...F` (a shared joint carries an
internal parent in at most one neighbour); a mixed word would give both end joints an internal parent, which is
impossible for a block-like group whose interior atoms have internal degree `4`
(`not_both_internalParent`).  So the spine is aligned, and the first (resp. last) member is the top ingredient.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem Spine.last_member {L : List (Finset V × V × V)} {U : Finset V} {a c : V} (h : Spine M L U a c) :
    ∃ T p, (T, p, c) ∈ L ∧ T ⊆ U := by
  cases h with
  | one hv => exact ⟨_, a, by simp, Finset.Subset.refl _⟩
  | snoc hs hT hi hne => exact ⟨_, _, List.mem_append_right _ (List.mem_singleton_self _), subset_union_right⟩

theorem Spine.first_member {L : List (Finset V × V × V)} {U : Finset V} {a c : V} (h : Spine M L U a c) :
    ∃ T q, (T, a, q) ∈ L := by
  induction h with
  | @one T a' b hv => exact ⟨T, b, by simp⟩
  | snoc _ _ _ _ ih =>
    obtain ⟨T, q, hm⟩ := ih
    exact ⟨T, q, List.mem_append_left _ hm⟩

end generic

variable {w : ℕ} {G : Garden w}

section orient
variable {D' : Type*} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}

/-- **Orientation of an all-(CL) spine**: all members aligned one way, or both end joints carry an internal parent. -/
theorem Spine.orient {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {U : Finset (GBranch G.tree)} {a c : GBranch G.tree} (hs : Spine N L U a c)
    (hcl : ∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q ∨ CLParentPattern G T q p) :
    (∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q) ∨ (∀ T p q, (T, p, q) ∈ L → CLParentPattern G T q p) ∨
      (InternalParent G U a ∧ InternalParent G U c) := by
  induction hs with
  | @one T a' b hv =>
    rcases hcl T a' b (by simp) with h | h
    · left
      intro T' p q hm
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      exact h
    · right; left
      intro T' p q hm
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      exact h
  | @snoc L' U' T a' b c' hs' hT hi hne ih =>
    have hcl' : ∀ T p q, (T, p, q) ∈ L' → CLParentPattern G T p q ∨ CLParentPattern G T q p :=
      fun T p q hm => hcl T p q (List.mem_append_left _ hm)
    have hnew := hcl T b c' (by simp)
    -- the new member cannot have an internal parent at `b` if the prefix has one
    have hconf : InternalParent G U' b → ¬ CLParentPattern G T c' b := fun h h' =>
      not_internalParent_of_inter hi h h'.2
    rcases ih hcl' with hF | hB | hmix
    · obtain ⟨Tl, pl, hml, hsub⟩ := hs'.last_member
      have hIP : InternalParent G U' b := internalParent_mono hsub (hF Tl pl b hml).2
      have hF' : CLParentPattern G T b c' := hnew.resolve_right (hconf hIP)
      left
      intro T'' p q hm
      rcases List.mem_append.mp hm with h | h
      · exact hF T'' p q h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact hF'
    · rcases hnew with hF' | hB'
      · right; right
        obtain ⟨T1, q1, hm1⟩ := hs'.first_member
        have h1 : InternalParent G U' a' :=
          internalParent_mono (hs'.mem_vine hm1).2 (hB T1 a' q1 hm1).2
        exact ⟨internalParent_mono subset_union_left h1, internalParent_mono subset_union_right hF'.2⟩
      · right; left
        intro T'' p q hm
        rcases List.mem_append.mp hm with h | h
        · exact hB T'' p q h
        · simp only [List.mem_singleton, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact hB'
    · right; right
      have hF' : CLParentPattern G T b c' := hnew.resolve_right (hconf hmix.2)
      exact ⟨internalParent_mono subset_union_left hmix.1, internalParent_mono subset_union_right hF'.2⟩

/-- Facts for a spine all of whose members have their upper joint on the left. -/
theorem Spine.allF_facts {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {U : Finset (GBranch G.tree)} {a c : GBranch G.tree} (hs : Spine N L U a c)
    (hblk : ∀ T p q, (T, p, q) ∈ L → G.molecule.IsBlock T p q)
    (hF : ∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q) :
    (∀ T p q, (T, p, q) ∈ L → a.toNode.IsDesc p.toNode) ∧ (∃ T q, (T, a, q) ∈ L) ∧
      (∀ T q T' q', (T, a, q) ∈ L → (T', a, q') ∈ L → T = T') := by
  induction hs with
  | @one T a' b hv =>
    refine ⟨?_, ⟨T, b, by simp⟩, ?_⟩
    · intro T' p q hm
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      exact ⟨rfl, List.prefix_refl _⟩
    · intro T1 q1 T2 q2 h1 h2
      simp only [List.mem_singleton, Prod.mk.injEq] at h1 h2
      exact h1.1.trans h2.1.symm
  | @snoc L' U' T a' b c' hs' hT hi hne ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (fun T p q hm => hblk T p q (List.mem_append_left _ hm))
      (fun T p q hm => hF T p q (List.mem_append_left _ hm))
    obtain ⟨Tl, pl, hml, _⟩ := hs'.last_member
    have hdl := (cl_parent_strict_descendant G (hblk Tl pl b (List.mem_append_left _ hml))
      (hF Tl pl b (List.mem_append_left _ hml))).1
    have hdb : a'.toNode.IsDesc b.toNode := ⟨(ih1 Tl pl b hml).1.trans hdl.1, (ih1 Tl pl b hml).2.trans hdl.2⟩
    have ha_ne : a' ≠ b := hs'.ends.2.2
    refine ⟨?_, ?_, ?_⟩
    · intro T'' p q hm
      rcases List.mem_append.mp hm with h | h
      · exact ih1 T'' p q h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact hdb
    · obtain ⟨T1, q1, hm1⟩ := ih2
      exact ⟨T1, q1, List.mem_append_left _ hm1⟩
    · intro T1 q1 T2 q2 h1 h2
      rcases List.mem_append.mp h1 with h1 | h1
      · rcases List.mem_append.mp h2 with h2 | h2
        · exact ih3 T1 q1 T2 q2 h1 h2
        · simp only [List.mem_singleton, Prod.mk.injEq] at h2
          exact absurd h2.2.1 ha_ne
      · simp only [List.mem_singleton, Prod.mk.injEq] at h1
        exact absurd h1.2.1 ha_ne

/-- The top ingredient of an all-F spine. -/
theorem top_of_allF {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {u v : GBranch G.tree} (hs : Spine N L S u v)
    (hvine : ∀ T p q, (T, p, q) ∈ L → Src.IsSomeVine Src.γL G.molecule T p q)
    (hF : ∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q)
    (hing : ∀ c' : CLVine G, IsIngredient G.molecule S c'.atoms →
      ∃ p q, (c'.atoms, p, q) ∈ L ∨ (c'.atoms, q, p) ∈ L) :
    ∃ t ∈ L, ∃ c : CLVine G, c.atoms = t.1 ∧ IsTopIngredient S c := by
  obtain ⟨h1, ⟨T0, q0, hm0⟩, h3⟩ := hs.allF_facts (fun T p q hm => (hvine T p q hm).block) hF
  have hcl0 := hF T0 u q0 hm0
  let c0 : CLVine G := ⟨T0, u, q0, hvine T0 u q0 hm0, hcl0.1, hcl0.2⟩
  refine ⟨(T0, u, q0), hm0, c0, rfl, ?_⟩
  intro c' hI hne
  obtain ⟨p, q, hpq⟩ := hing c' hI
  obtain ⟨p', q', hm'⟩ : ∃ p' q', (c'.atoms, p', q') ∈ L := by
    rcases hpq with h | h
    · exact ⟨p, q, h⟩
    · exact ⟨q, p, h⟩
  have hdesc := h1 c'.atoms p' q' hm'
  have hcl' := hF c'.atoms p' q' hm'
  have hup : c'.upper = p' := by
    have hX := c'.isVine
    have hY := hvine c'.atoms p' q' hm'
    have hj := Vine.block_joints_unique G.molecule hX.block hY.block
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact e1
    · exfalso
      have hnp : ¬ Mole.InternalParent G c'.atoms c'.upper := c'.notParentUpper
      rw [e1] at hnp
      exact hnp hcl'.2
  have hpu : p' ≠ u := by
    intro h
    subst h
    exact hne (h3 _ _ _ _ hm' hm0)
  rw [hup]
  exact ⟨Ne.symm hpu, hdesc⟩

end orient

/-- **An HVC group whose ingredients are all (CL) has a top ingredient** (TARGET L1935; the degenerate case of
`hvc_group` does not occur). -/
theorem hvc_top_exists (hM : G.molecule.IsMolecule) {e : GardenDart G} {a b : GBranch G.tree}
    {S : Finset (GBranch G.tree)}
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    (hends : G.molecule.ends e = s(a, b)) (hBe : (eraseBond G.molecule e).IsBlock S a b)
    (hs : Spine (eraseBond G.molecule e) L S a b) (hlen : 2 ≤ L.length)
    (hnon : ∀ t ∈ L, ¬ CNMem G t) :
    ∃ t ∈ L, ∃ c : CLVine G, c.atoms = t.1 ∧ IsTopIngredient S c := by
  have hVineM : ∀ T p q, (T, p, q) ∈ L → Src.IsSomeVine Src.γL G.molecule T p q := fun T p q hm =>
    (vine_transfer G.molecule hends (hs.not_both hlen hm) p q).mp (hs.mem_vine hm).1
  have hcl : ∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q ∨ CLParentPattern G T q p := by
    intro T p q hm
    have hX := hVineM T p q hm
    rcases block_parent_patterns G hX.block with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hnon _ hm)
  have hing : ∀ c' : CLVine G, IsIngredient G.molecule S c'.atoms →
      ∃ p q, (c'.atoms, p, q) ∈ L ∨ (c'.atoms, q, p) ∈ L := fun c' h =>
    isIngredient_hvc hM hends hBe hs hlen h
  rcases hs.orient hcl with hF | hB | hmix
  · exact top_of_allF hs hVineM hF hing
  · have hs' := hs.reverse
    obtain ⟨t, ht, c, hc, htop⟩ := top_of_allF hs'
      (fun T p q hm => isSomeVine_swap (hVineM T q p (mem_revSwap.mp hm)))
      (fun T p q hm => hB T q p (mem_revSwap.mp hm))
      (by
        intro c' hI
        obtain ⟨p, q, h⟩ := hing c' hI
        rcases h with h | h
        · exact ⟨q, p, Or.inl (mem_revSwap.mpr h)⟩
        · exact ⟨q, p, Or.inr (mem_revSwap.mpr h)⟩)
    obtain ⟨T, p, q⟩ := t
    exact ⟨(T, q, p), mem_revSwap.mp ht, c, hc, htop⟩
  · exfalso
    obtain ⟨_, _, hint⟩ := hyperBlock_degrees G.molecule (⟨e, hends, hBe⟩ : G.molecule.IsHyperBlock S a b)
    exact not_both_internalParent hint hmix

end WaveTurbulence.GammaLow.FinalCount.H
