/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceRunsMK3` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK2
import Mathlib.Tactic
public import WaveTurbulence.Foundations.FinalCount.RedSpliceRunsMK3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceRunsMK
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# B2a MK-RUNS: `Nonempty (MarkedGroupUnits γ G S Mk)` for every marked group

* `markedGroupUnits_of_spineMK`: the runs (`runs_of_spineMK`) and survivors (the members that are not unmarked-`𝒱`)
  of a spine of the group `S` with at least one survivor form a `MarkedGroupUnits γ G S Mk`;
* `exists_markedGroupUnits`: every marked group (`markedGroup γ G Mk S`) is a VC or an HVC with a marked ingredient,
  hence has one (no maximality of `S` is needed).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]


section core
variable {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {Mk : Set (CLVineG γ G)}

/-- **The runs and survivors of a spine with a survivor.** -/
theorem markedGroupUnits_of_spineMK (hN : N.IsMolecule) (hs : Spine γ N L S a b) (hB : N.IsBlock S a b)
    (hrun : ∀ X x y, X ⊆ S → ¬ (a ∈ X ∧ b ∈ X) → N.IsBlock X x y → G.molecule.IsBlock X x y)
    (hvineM : ∀ t ∈ L, Src.IsSomeVine γ G.molecule t.1 t.2.1 t.2.2)
    (hingr : ∀ t ∈ L, IsIngredientG γ G.molecule S t.1)
    (hmemb : ∀ T, IsIngredientG γ G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
    (hsurv : ∃ t ∈ L, ¬ UnmMemMK γ G Mk t) : Nonempty (MarkedGroupUnits γ G S Mk) := by
  classical
  obtain ⟨runs, hruns, hdisj, hcov⟩ := runs_of_spineMK hN hs hB hrun hvineM hingr hsurv
  -- every ingredient is a member, read with its atoms
  have hmem1 : ∀ T, IsIngredientG γ G.molecule S T → ∃ t ∈ L, t.1 = T := by
    intro T hT
    obtain ⟨p, q, h | h⟩ := hmemb T hT
    · exact ⟨_, h, rfl⟩
    · exact ⟨_, h, rfl⟩
  have hcover : ∀ c : CLVineG γ G, c ∈ vinesVG γ G → c ∉ Mk → IsIngredientG γ G.molecule S c.atoms →
      ∃ u ∈ runs, c.atoms ⊆ u.atoms := by
    intro c hc hcMk hci
    obtain ⟨t, ht, htc⟩ := hmem1 _ hci
    obtain ⟨u, hu, hsub⟩ := hcov t ht ⟨c, hc, hcMk, htc.symm⟩
    exact ⟨u, hu, htc ▸ hsub⟩
  refine ⟨{
    runs := runs
    surv := L.filter (fun t => ¬ UnmMemMK γ G Mk t)
    sub := fun u hu => (hruns u hu).1.1
    disj := hdisj
    sound := ?_
    cover := hcover
    maximal := ?_
    surv_spec := ?_
    surv_cover := ?_
    partition := ?_
    surv_meet := ?_
    ext := fun u hu => (hruns u hu).1.2.2
    chain := ?_
    spine := fun u hu => (hruns u hu).1.2.1
    surv_skip := ?_
    surv_spine := ⟨D', inferInstance, inferInstance, N, L, a, b, hN, hs, hB, hrun, hvineM, hingr, hmemb,
      List.filter_sublist, fun t ht => by simp [List.mem_filter, ht, UnmMemMK]⟩ }⟩
  · intro u hu
    obtain ⟨R, hsR, hR⟩ := (hruns u hu).1.2.1
    obtain ⟨cs, hcs1, hcs2⟩ := choose_listMK (P := fun t (c : CLVineG γ G) =>
      c ∈ vinesVG γ G ∧ c ∉ Mk ∧ IsIngredientG γ G.molecule S c.atoms ∧ c.atoms = t.1) R hR
    refine ⟨cs, fun c hc => ?_, fun v => ?_⟩
    · obtain ⟨t, -, h1, h2, h3, -⟩ := hcs1 c hc
      exact ⟨h1, h2, h3⟩
    · rw [hsR.mem_iff v]
      constructor
      · rintro ⟨t, ht, hv⟩
        obtain ⟨c, hc, -, -, -, hct⟩ := hcs2 t ht
        exact ⟨c, hc, hct ▸ hv⟩
      · rintro ⟨c, hc, hv⟩
        obtain ⟨t, ht, -, -, -, hct⟩ := hcs1 c hc
        exact ⟨t, ht, hct ▸ hv⟩
  · intro u hu c hc hcMk hci hnd
    obtain ⟨u', hu', hsub⟩ := hcover c hc hcMk hci
    by_cases huu : u' = u
    · exact huu ▸ hsub
    · exfalso
      obtain ⟨v, hvc, hvu⟩ := Finset.not_disjoint_iff.mp hnd
      have hdj := pairwise_symm_forallMK (fun x y h => Disjoint.symm h) hdisj hu' hu huu
      exact Finset.disjoint_left.mp hdj (hsub hvc) hvu
  · intro t ht
    obtain ⟨htL, htg⟩ := List.mem_filter.mp ht
    have htg' : ¬ UnmMemMK γ G Mk t := by simpa using htg
    refine ⟨hvineM t htL, hingr t htL, ?_⟩
    by_cases hex : ∃ c ∈ vinesVG γ G, c.atoms = t.1
    · obtain ⟨c, hcV, hct⟩ := hex
      refine Or.inl ⟨c, ?_, hcV, hct⟩
      by_contra hcMk
      exact htg' ⟨c, hcV, hcMk, hct⟩
    · push Not at hex
      exact Or.inr hex
  · intro c hcMk hcV hci
    obtain ⟨t, ht, htc⟩ := hmem1 _ hci
    refine ⟨t, List.mem_filter.mpr ⟨ht, ?_⟩, htc⟩
    simp only [decide_eq_true_eq]
    rintro ⟨c', hc'V, hc'Mk, hc't⟩
    exact hc'Mk ((clvine_eq_of_atomsMK (hc't.trans htc)) ▸ hcMk)
  · intro v hv
    obtain ⟨t, ht, hvt⟩ := (hs.mem_iff v).mp hv
    by_cases hg : UnmMemMK γ G Mk t
    · obtain ⟨u, hu, hsub⟩ := hcov t ht hg
      exact Or.inl ⟨u, hu, hsub hvt⟩
    · exact Or.inr ⟨t, List.mem_filter.mpr ⟨ht, by simpa using hg⟩, hvt⟩
  · exact hs.pairwise_interMK.sublist List.filter_sublist
  · intro u hu
    obtain ⟨R, hsR, -⟩ := (hruns u hu).1.2.1
    exact ⟨_, hsR.chain⟩
  · intro T hT hno
    obtain ⟨t, ht, htT⟩ := hmem1 T hT
    refine ⟨t, List.mem_filter.mpr ⟨ht, ?_⟩, htT⟩
    simp only [decide_eq_true_eq]
    rintro ⟨c, hcV, -, hct⟩
    exact hno c hcV (hct.trans htT)

end core

/-- **Runs and survivors exist for every marked group** (o75 §2.5): a group with a marked `𝒱`-ingredient is a VC
or an HVC, and its spine (in the molecule, resp. its adjoint) is cut into maximal runs of unmarked `𝒱`-ingredients
and the survivors between them. -/
theorem exists_markedGroupUnits {Mk : Set (CLVineG γ G)} {S : Finset (GBranch G.tree)}
    (hmk : markedGroup γ G Mk S) : Nonempty (MarkedGroupUnits γ G S Mk) := by
  classical
  have hM : G.molecule.IsMolecule := Mole.garden_isMolecule G
  obtain ⟨c, hcMk, hcV, hci⟩ := hmk
  -- the marked ingredient is a survivor of any spine having it as a member
  have hsurv : ∀ L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree),
      (∀ T, IsIngredientG γ G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L) →
      ∃ t ∈ L, ¬ UnmMemMK γ G Mk t := by
    intro L hmemb
    obtain ⟨p, q, h | h⟩ := hmemb _ hci <;>
    · refine ⟨_, h, ?_⟩
      rintro ⟨c', -, hc'Mk, hc't⟩
      exact hc'Mk ((clvine_eq_of_atomsMK hc't) ▸ hcMk)
  have hci' := hci
  rcases hci' with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, hends, hn2, hBe, hI⟩
  · -- a VC: the spine lives in the garden molecule
    obtain ⟨L, hs⟩ := Spine.of_chain (chainIngredientG_spec hI).1
    have hmemb : ∀ T, IsIngredientG γ G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L :=
      fun T hT => isIngredient_vc hM hB hs hT
    refine markedGroupUnits_of_spineMK hM hs hB (fun X x y _ _ h => h) ?_ ?_ hmemb (hsurv L hmemb)
    · intro ⟨T, p, q⟩ ht
      exact (hs.mem_vine ht).1
    · intro ⟨T, p, q⟩ ht
      exact Or.inl ⟨a, b, L.length, p, q, hB, hs.ingredient_of_mem ht⟩
  · -- an HVC: the spine lives in the adjoint `eraseBond G.molecule e`
    have hab : a ≠ b := hBe.2.2.2.1
    have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
      intro h
      unfold Molecule.ends at hends
      rw [h] at hends
      rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab (h1.symm.trans h2)
      · exact hab (h2.symm.trans h1)
    have hN := eraseBond_isMolecule G.molecule hM e hne
    obtain ⟨L, hs, hlen⟩ := Spine.of_chain_len (chainIngredientG_spec hI).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn2
    have hmemb : ∀ T, IsIngredientG γ G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L :=
      fun T hT => isIngredient_hvc hM hends hBe hs hlen2 hT
    refine markedGroupUnits_of_spineMK hN hs hBe
      (fun X x y _ hX h => (block_transfer G.molecule hends hX x y).mp h) ?_ ?_ hmemb (hsurv L hmemb)
    · intro ⟨T, p, q⟩ ht
      exact (vine_transfer G.molecule hends (hs.not_both hlen2 ht) p q).mp (hs.mem_vine ht).1
    · intro ⟨T, p, q⟩ ht
      exact Or.inr ⟨a, b, e, L.length, p, q, hends, hlen2, hBe, hs.ingredient_of_mem ht⟩

end WaveTurbulence.GammaLow.Fama
