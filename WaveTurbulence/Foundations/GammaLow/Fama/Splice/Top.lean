/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceTop` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceTop


/-!
# REDSPLICE-DEF (S2a): the top ingredient of an all-(CL) block chain

In a block chain `T_1, ..., T_m` of (CL) vines whose union has no internal parent at the end joint `a`, every
ingredient is aligned with its upper joint on the `a` side (`Spine.cl_aligned`): a shared joint cannot carry an
internal parent in both neighbours.  So the first ingredient is the unique one whose upper joint is a strict
ancestor of all the others (`Spine.top_exists`; TARGET L1935, the `top' vine).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input]

/-- A member of a spine is an ingredient of the underlying chain, and conversely. -/
theorem Spine.ingredient_mem {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (hM : M.IsMolecule) {L : List (Finset V × V × V)} {U : Finset V} {a b : V} {n : ℕ}
    {A : Finset V} {p q : V} (hs : Spine γ M L U a b) (hB : M.IsBlock U a b)
    (hI : ChainIngredientG γ M U a b n A p q) : (A, p, q) ∈ L := by
  obtain ⟨L', hL', hm⟩ := Spine.mem_of_ingredient hI
  rwa [Spine.unique hM hL' hs hB] at hm

/-- **Alignment of an all-(CL) spine.** -/
theorem Spine.cl_aligned (hM : G.molecule.IsMolecule) {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {U : Finset (GBranch G.tree)} {a c : GBranch G.tree} (hs : Spine γ G.molecule L U a c)
    (hcl : ∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q ∨ CLParentPattern G T q p)
    (hB : G.molecule.IsBlock U a c) (hP0 : ¬ InternalParent G U a) :
    (∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q ∧ a.toNode.IsDesc p.toNode ∧ (a ∈ T → p = a)) ∧
    (∃ T q, (T, a, q) ∈ L) ∧ (∀ T q T' q', (T, a, q) ∈ L → (T', a, q') ∈ L → T = T') := by
  induction hs with
  | @one T a' b hv =>
    have hc := hcl T a' b (by simp)
    have hcl' : CLParentPattern G T a' b := by
      rcases hc with hc | hc
      · exact hc
      · exact absurd hc.2 hP0
    refine ⟨?_, ⟨T, b, by simp⟩, ?_⟩
    · intro T' p q hm
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm
      exact ⟨hcl', ⟨rfl, List.prefix_refl _⟩, fun _ => rfl⟩
    · intro T1 q1 T2 q2 h1 h2
      simp only [List.mem_singleton, Prod.mk.injEq] at h1 h2
      exact h1.1.trans h2.1.symm
  | @snoc L' U' T' a' b c' hs' hT hi hne ih =>
    have hBU' : G.molecule.IsBlock U' a' b := chain_prefix_isBlock G.molecule hM hs'.chain hT hi hB
    have hP0' : ¬ InternalParent G U' a' := fun h => hP0 (RedSplice.internalParent_mono subset_union_left h)
    have hcl' : ∀ T p q, (T, p, q) ∈ L' → CLParentPattern G T p q ∨ CLParentPattern G T q p :=
      fun T p q hm => hcl T p q (List.mem_append_left _ hm)
    obtain ⟨ih1, ih2, ih3⟩ := ih hcl' hBU' hP0'
    -- the prefix has an internal parent at its right joint
    have hIPb : InternalParent G U' b := by
      have hcI : ∀ A p q, ChainIngredientG γ G.molecule U' a' b L'.length A p q →
          CLParentPattern G A p q ∨ CLParentPattern G A q p := fun A p q hI =>
        hcl' A p q (hs'.ingredient_mem hM hBU' hI)
      rcases chain_cl_end_parent hM hs'.chain hcI hBU' with h | h
      · exact absurd h hP0'
      · exact h
    have hPre : CLParentPattern G U' a' b := ⟨hP0', hIPb⟩
    have hdesc : a'.toNode.IsDesc b.toNode := (cl_parent_strict_descendant G hBU' hPre).1
    have hnew : CLParentPattern G T' b c' := by
      rcases hcl T' b c' (by simp) with h | h
      · exact h
      · exact absurd (not_internalParent_of_inter hi hIPb h.2) id
    have ha_ne : a' ≠ b := hs'.ends.2.2
    refine ⟨?_, ?_, ?_⟩
    · intro T p q hm
      rcases List.mem_append.mp hm with h | h
      · obtain ⟨x1, x2, x3⟩ := ih1 T p q h
        exact ⟨x1, x2, x3⟩
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨hnew, hdesc, fun ha => ?_⟩
        exfalso
        have : a' ∈ U' ∩ T := mem_inter.mpr ⟨hs'.ends.1, ha⟩
        rw [hi] at this
        exact ha_ne (mem_singleton.mp this)
    · obtain ⟨T, q, hm⟩ := ih2
      exact ⟨T, q, List.mem_append_left _ hm⟩
    · intro T1 q1 T2 q2 h1 h2
      rcases List.mem_append.mp h1 with h1 | h1
      · rcases List.mem_append.mp h2 with h2 | h2
        · exact ih3 T1 q1 T2 q2 h1 h2
        · simp only [List.mem_singleton, Prod.mk.injEq] at h2
          exact absurd h2.2.1 ha_ne
      · simp only [List.mem_singleton, Prod.mk.injEq] at h1
        exact absurd h1.2.1 ha_ne


theorem mem_revSwap {V : Type*} {L : List (Finset V × V × V)} {T : Finset V} {x y : V} :
    (T, x, y) ∈ L.reverse.map (fun t => (t.1, t.2.2, t.2.1)) ↔ (T, y, x) ∈ L := by
  simp only [List.mem_map, List.mem_reverse, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨T', p, q, hm, rfl, rfl, rfl⟩
    exact hm
  · intro h
    exact ⟨T, y, x, h, rfl, rfl, rfl⟩

/-- The top ingredient from an aligned spine. -/
theorem top_of_spine (hM : G.molecule.IsMolecule)
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {u v : GBranch G.tree} (hs : Spine γ G.molecule L S u v)
    (hB : G.molecule.IsBlock S u v) (hnon : ∀ T p q, (T, p, q) ∈ L → ¬ CNMem G (T, p, q))
    (hu : ¬ InternalParent G S u)
    (hing : ∀ c' : CLVineG γ G, IsIngredientG γ G.molecule S c'.atoms →
      ∃ p q, (c'.atoms, p, q) ∈ L ∨ (c'.atoms, q, p) ∈ L) :
    ∃ t ∈ L, ∃ c : CLVineG γ G, c.atoms = t.1 ∧ IsTopIngredientG S c := by
  classical
  have hcl : ∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q ∨ CLParentPattern G T q p := by
    intro T p q hm
    have hb := (hs.mem_vine hm).1
    rcases block_parent_patterns G (Src.isBlock_of_isSomeVine hb) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hnon T p q hm)
  obtain ⟨h1, ⟨T0, q0, hm0⟩, h3⟩ := hs.cl_aligned hM hcl hB hu
  have hv0 := (hs.mem_vine hm0).1
  obtain ⟨hcl0, _, _⟩ := h1 T0 u q0 hm0
  let c0 : CLVineG γ G := ⟨T0, u, q0, hv0, hcl0.1, hcl0.2⟩
  refine ⟨(T0, u, q0), hm0, c0, rfl, ?_⟩
  intro c' hI hne
  obtain ⟨p, q, hpq⟩ := hing c' hI
  -- a member of the spine with the atoms of `c'`
  obtain ⟨p', q', hm'⟩ : ∃ p' q', (c'.atoms, p', q') ∈ L := by
    rcases hpq with h | h
    · exact ⟨p, q, h⟩
    · exact ⟨q, p, h⟩
  obtain ⟨hcl', hdesc, _⟩ := h1 c'.atoms p' q' hm'
  -- the upper joint of `c'` is `p'`
  have hup : c'.upper = p' := by
    have hj := Vine.block_joints_unique G.molecule (Src.isBlock_of_isSomeVine c'.isVine)
      (Src.isBlock_of_isSomeVine (hs.mem_vine hm').1)
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


/-- **A root VC with only (CL) ingredients has a top ingredient** (TARGET L1935). -/
theorem vc_top_exists (hM : G.molecule.IsMolecule)
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (hs : Spine γ G.molecule L S a b)
    (hB : G.molecule.IsBlock S a b) (hnon : ∀ t ∈ L, ¬ CNMem G t) (hroot : IsRootVCG γ G S) :
    ∃ t ∈ L, ∃ c : CLVineG γ G, c.atoms = t.1 ∧ IsTopIngredientG S c := by
  classical
  obtain ⟨a', b', hvc, hpat, _⟩ := hroot
  have hj := Vine.block_joints_unique G.molecule hvc.1 hB
  have hing : ∀ c' : CLVineG γ G, IsIngredientG γ G.molecule S c'.atoms →
      ∃ p q, (c'.atoms, p, q) ∈ L ∨ (c'.atoms, q, p) ∈ L := fun c' h => isIngredient_vc hM hB hs h
  -- the joint `u` without internal parent is `a` or `b`
  have hcases : (¬ InternalParent G S a) ∨ (¬ InternalParent G S b) := by
    rcases hpat with h | h
    · rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl (h1 ▸ h.1)
      · exact Or.inr (h1 ▸ h.1)
    · rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨_, h2⟩ | ⟨_, h2⟩
      · exact Or.inr (h2 ▸ h.1)
      · exact Or.inl (h2 ▸ h.1)
  rcases hcases with hu | hu
  · exact top_of_spine hM hs hB (fun T p q hm => hnon _ hm) hu hing
  · have hs' := hs.reverse
    have hB' := block_swap_joints G.molecule hB
    obtain ⟨t, ht, c, hc, htop⟩ := top_of_spine hM hs' hB' (by
      intro T p q hm
      exact hnon (T, q, p) (mem_revSwap.mp hm) |> fun h h' => h ⟨h'.2, h'.1⟩) hu (by
      intro c' hI
      obtain ⟨p, q, h⟩ := hing c' hI
      rcases h with h | h
      · exact ⟨q, p, Or.inl (mem_revSwap.mpr h)⟩
      · exact ⟨q, p, Or.inr (mem_revSwap.mpr h)⟩)
    obtain ⟨T, p, q⟩ := t
    exact ⟨(T, q, p), mem_revSwap.mp ht, c, hc, htop⟩

end WaveTurbulence.GammaLow.Fama
