/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceHVC` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Local
public import WaveTurbulence.Foundations.Molecule.VineEraseBondMolecule
public import WaveTurbulence.Foundations.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.Molecule.VineLocalDartErasure
public import WaveTurbulence.Foundations.Molecule.VineLocalDartObjects
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHVC


/-!
# REDSPLICE-DEF (S2a): the units of an HVC group

An HVC `S` is a block chain of the adjoint molecule `eraseBond M e` (the bond `e` joins the end joints `a, b`).
The spine `L` of `S` is taken in the adjoint; no ingredient contains both `a` and `b`, so each ingredient and each
run avoiding one of the ends is a block (vine) of `M` itself (`Vine.LocalDartEmbedding`).  Hence the runs around the
skipped ingredient (the (CN) one, else the top one) are (CL) blocks of the garden.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input]

section transfer
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

theorem vine_transfer {e : D} {a b : V} (hends : M.ends e = s(a, b)) {X : Finset V}
    (hX : ¬ (a ∈ X ∧ b ∈ X)) (x y : V) : Src.IsSomeVine γ (eraseBond M e) X x y ↔ Src.IsSomeVine γ M X x y :=
  LocalDart.isVineGamma_iff (eraseBond_local_embedding M e X (RedSplice.not_inGroup_of_ends M hends hX)) γ X
    (subset_refl X) x y

end transfer

/-- In a spine of length at least two no member contains both end joints. -/
theorem Spine.not_both {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {L : List (Finset V × V × V)} {U : Finset V} {a c : V} (h : Spine γ M L U a c) (hlen : 2 ≤ L.length)
    {T : Finset V} {p q : V} (hm : (T, p, q) ∈ L) : ¬ (a ∈ T ∧ c ∈ T) := by
  rcases h.inv with ⟨T0, rfl, _⟩ | ⟨L', U', T', b, rfl, hU, hS, hT, hi, hne⟩
  · simp at hlen
  · rintro ⟨ha, hc⟩
    rcases List.mem_append.mp hm with h1 | h1
    · have hsub := (hS.mem_vine h1).2
      have : c ∈ U' ∩ T' := mem_inter.mpr ⟨hsub hc, (isSomeVine_ends hT).2.1⟩
      rw [hi] at this
      exact (isSomeVine_ends hT).2.2 (mem_singleton.mp this).symm
    · simp only [List.mem_singleton, Prod.mk.injEq] at h1
      obtain ⟨rfl, _, _⟩ := h1
      have : a ∈ U' ∩ T := mem_inter.mpr ⟨hS.ends.1, ha⟩
      rw [hi] at this
      exact hS.ends.2.2 (mem_singleton.mp this)

theorem Spine.of_chain_len {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    {U : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M U a b n) : ∃ L, Spine γ M L U a b ∧ L.length = n := by
  induction h with
  | single hv => exact ⟨_, Spine.one hv, rfl⟩
  | append _ hT hi hne ih =>
    obtain ⟨L, hL, hlen⟩ := ih
    exact ⟨_, Spine.snoc hL hT hi hne, by simp [hlen]⟩

/-- A non-(CN) ingredient of an HVC group lies in `𝒱` under the (CN)/top conditions of `defcong`. -/
theorem member_mem_vinesV_hvc {S : Finset (GBranch G.tree)} (hSmax : S ∈ maximalGroupsG γ G.molecule)
    (hhvc : ∃ a b, Src.IsHVC γ G.molecule S a b) {a b : GBranch G.tree}
    {e : GardenDart G} (hends : G.molecule.ends e = s(a, b)) (hBe : (eraseBond G.molecule e).IsBlock S a b)
    {n : ℕ} (hn2 : 2 ≤ n) {T : Finset (GBranch G.tree)} {p q : GBranch G.tree}
    (hI : ChainIngredientG γ (eraseBond G.molecule e) S a b n T p q)
    (hvine : Src.IsSomeVine γ G.molecule T p q) (hnon : ¬ CNMem G (T, p, q))
    (hcond : (∃ T', IsIngredientG γ G.molecule S T' ∧ IsCNVineG γ G T') ∨
      ∀ c : CLVineG γ G, c.atoms = T → ¬ IsTopIngredientG S c) :
    ∃ c ∈ vinesVG γ G, c.atoms = T ∧ IsIngredientG γ G.molecule S T := by
  obtain ⟨c, hc1, _⟩ := exists_clVine hvine hnon
  have hingr : IsIngredientG γ G.molecule S T := Or.inr ⟨a, b, e, n, p, q, hends, hn2, hBe, hI⟩
  refine ⟨c, ⟨S, hSmax, hc1 ▸ hingr, Or.inr ⟨Or.inl hhvc, ?_⟩⟩, hc1, hingr⟩
  rcases hcond with h | h
  · exact Or.inl h
  · exact Or.inr (h c hc1)

/-- The specification of the units of an HVC group. -/
@[expose] def HVCSplitSpec (γ : ℝ) (G : Garden w) (e : GardenDart G) (S : Finset (GBranch G.tree))
    (a b : GBranch G.tree)
    (L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)) : Prop :=
  (∃ (A : Finset (GBranch G.tree)) (x y : GBranch G.tree), (A, x, y) ∈ L ∧
    Src.IsSomeVine γ G.molecule A x y ∧ IsIngredientG γ G.molecule S A ∧
    (G.molecule.ends e = s(a, b) ∧ (eraseBond G.molecule e).IsBlock S a b ∧ (eraseBond G.molecule e).IsMolecule ∧
      Src.IsSomeVine γ (eraseBond G.molecule e) A x y) ∧
    Nonempty (RunCut γ G (eraseBond G.molecule e) L S a b A x y) ∧
    (∀ t ∈ L, t ≠ (A, x, y) → ∃ c ∈ vinesVG γ G, c.atoms = t.1 ∧ IsIngredientG γ G.molecule S t.1) ∧
    (CNMem G (A, x, y) ∨ ((∀ t ∈ L, ¬ CNMem G t) ∧
      ∃ c : CLVineG γ G, c.atoms = A ∧ IsTopIngredientG S c))) ∨
  (G.molecule.ends e = s(a, b) ∧ (eraseBond G.molecule e).IsBlock S a b ∧
    (∀ t ∈ L, ¬ CNMem G t) ∧ ∀ t ∈ L, ∀ c : CLVineG γ G, c.atoms = t.1 → ¬ IsTopIngredientG S c)

/-- **The units of an HVC group** (TARGET L1934-L1937). -/
theorem hvc_group (hM : G.molecule.IsMolecule) {S : Finset (GBranch G.tree)}
    (hSmax : S ∈ maximalGroupsG γ G.molecule) {a b : GBranch G.tree}
    (hhvc : Src.IsHVC γ G.molecule S a b) :
    ∃ (e : GardenDart G) (L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)),
      ∃ _ : Spine γ (eraseBond G.molecule e) L S a b, 2 ≤ L.length ∧ HVCSplitSpec γ G e S a b L := by
  have hhvc' := hhvc
  obtain ⟨e, hends, hBe, n, hn2, hn⟩ := hhvc
  have hab : a ≠ b := hBe.2.2.2.1
  have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
    intro h
    unfold Molecule.ends at hends
    rw [h] at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab (h1.symm.trans h2)
    · exact hab (h2.symm.trans h1)
  have hN := eraseBond_isMolecule G.molecule hM e hne
  obtain ⟨L, hs, hlen⟩ := Spine.of_chain_len hn
  have hlen2 : 2 ≤ L.length := hlen ▸ hn2
  refine ⟨e, L, hs, hlen2, ?_⟩
  have hVineM : ∀ T p q, (T, p, q) ∈ L → Src.IsSomeVine γ G.molecule T p q := fun T p q hm =>
    (vine_transfer G.molecule hends (hs.not_both hlen2 hm) p q).mp (hs.mem_vine hm).1
  have hblk : ∀ T p q, (T, p, q) ∈ L → G.molecule.IsBlock T p q :=
    fun T p q hm => Src.isBlock_of_isSomeVine (hVineM T p q hm)
  have hrun : ∀ X x y, X ⊆ S → ¬ (a ∈ X ∧ b ∈ X) → (eraseBond G.molecule e).IsBlock X x y →
      G.molecule.IsBlock X x y := fun X x y _ hX h => (block_transfer G.molecule hends hX x y).mp h
  have hing : ∀ T p q, (T, p, q) ∈ L → ChainIngredientG γ (eraseBond G.molecule e) S a b n T p q :=
    fun T p q hm => hlen ▸ hs.ingredient_of_mem hm
  have hisI : ∀ T p q, (T, p, q) ∈ L → IsIngredientG γ G.molecule S T :=
    fun T p q hm => Or.inr ⟨a, b, e, n, p, q, hends, hn2, hBe, hing T p q hm⟩
  have hex : ∃ a b, Src.IsHVC γ G.molecule S a b := ⟨a, b, hhvc'⟩
  by_cases hcn : ∃ t ∈ L, CNMem G t
  · obtain ⟨⟨A, x, y⟩, hmem, hc⟩ := hcn
    have hnon : ∀ t ∈ L, t ≠ (A, x, y) → ¬ CNMem G t := fun t ht hne hct =>
      hne (hs.cn_unique hblk ht hmem hct hc)
    obtain ⟨rc⟩ := group_split hN hs hBe hrun hmem hnon
    refine Or.inl ⟨A, x, y, hmem, hVineM A x y hmem, hisI A x y hmem, ⟨hends, hBe, hN, (hs.mem_vine hmem).1⟩, ⟨rc⟩, ?_, Or.inl hc⟩
    intro t ht hne
    obtain ⟨T, p, q⟩ := t
    exact member_mem_vinesV_hvc hSmax hex hends hBe hn2 (hing T p q ht) (hVineM T p q ht)
      (hnon _ ht hne) (Or.inl ⟨A, hisI A x y hmem, x, y, hVineM A x y hmem, hc.1, hc.2⟩)
  · have hnon : ∀ t ∈ L, ¬ CNMem G t := fun t ht hct => hcn ⟨t, ht, hct⟩
    by_cases htop : ∃ t ∈ L, ∃ c : CLVineG γ G, c.atoms = t.1 ∧ IsTopIngredientG S c
    · obtain ⟨⟨A, x, y⟩, hmem, c0, hc0, hc0top⟩ := htop
      obtain ⟨rc⟩ := group_split hN hs hBe hrun hmem (fun t ht _ => hnon t ht)
      refine Or.inl ⟨A, x, y, hmem, hVineM A x y hmem, hisI A x y hmem, ⟨hends, hBe, hN, (hs.mem_vine hmem).1⟩, ⟨rc⟩, ?_, Or.inr ⟨hnon, c0, hc0, hc0top⟩⟩
      intro t ht hne
      obtain ⟨T, p, q⟩ := t
      refine member_mem_vinesV_hvc hSmax hex hends hBe hn2 (hing T p q ht) (hVineM T p q ht)
        (hnon _ ht) (Or.inr ?_)
      intro c hc hctop
      have hxy := isSomeVine_ends (hs.mem_vine hmem).1
      have hAT : T ≠ A := rc.atoms_ne hxy ht hne
      have hc0' : c0.atoms = A := hc0
      refine top_unique hctop hc0top (hc ▸ hisI T p q ht) (hc0' ▸ hisI A x y hmem) ?_
      rw [hc, hc0']
      exact hAT
    · refine Or.inr ⟨hends, hBe, hnon, ?_⟩
      intro t ht c hc hct
      exact htop ⟨t, ht, c, hc, hct⟩

end WaveTurbulence.GammaLow.Fama
