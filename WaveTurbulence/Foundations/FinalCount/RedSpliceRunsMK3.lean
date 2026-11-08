/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceRunsMK2
import Mathlib.Tactic

/-!
# B2a MK-RUNS: `Nonempty (MarkedGroupUnits G S Mk)` for every marked group

* `markedGroupUnits_of_spineMK`: the runs (`runs_of_spineMK`) and survivors (the members that are not unmarked-`𝒱`)
  of a spine of the group `S` with at least one survivor form a `MarkedGroupUnits G S Mk`;
* `exists_markedGroupUnits`: every marked group (`markedGroup G Mk S`) is a VC or an HVC with a marked ingredient,
  hence has one (no maximality of `S` is needed).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1

variable {w : ℕ} {G : Garden w}

/-- A symmetric pairwise relation holds between any two distinct elements. -/
theorem pairwise_symm_forallMK {α : Type*} {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: xs, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha | ha <;> rcases List.mem_cons.mp hb with hb | hb
    · exact absurd (ha.trans hb.symm) hne
    · exact ha ▸ h.1 b hb
    · exact hb ▸ hR _ _ (h.1 a ha)
    · exact pairwise_symm_forallMK hR h.2 ha hb hne

section core
variable {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {S : Finset (GBranch G.tree)}
  {a b : GBranch G.tree} {Mk : Set (CLVine G)}

/-- **The runs and survivors of a spine with a survivor.** -/
theorem markedGroupUnits_of_spineMK (hN : N.IsMolecule) (hs : Spine N L S a b) (hB : N.IsBlock S a b)
    (hrun : ∀ X x y, X ⊆ S → ¬ (a ∈ X ∧ b ∈ X) → N.IsBlock X x y → G.molecule.IsBlock X x y)
    (hvineM : ∀ t ∈ L, IsSomeVine G.molecule t.1 t.2.1 t.2.2)
    (hingr : ∀ t ∈ L, IsIngredient G.molecule S t.1)
    (hmemb : ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
    (hsurv : ∃ t ∈ L, ¬ UnmMemMK G Mk t) : Nonempty (MarkedGroupUnits G S Mk) := by
  classical
  obtain ⟨runs, hruns, hdisj, hcov⟩ := runs_of_spineMK hN hs hB hrun hvineM hingr hsurv
  -- every ingredient is a member, read with its atoms
  have hmem1 : ∀ T, IsIngredient G.molecule S T → ∃ t ∈ L, t.1 = T := by
    intro T hT
    obtain ⟨p, q, h | h⟩ := hmemb T hT
    · exact ⟨_, h, rfl⟩
    · exact ⟨_, h, rfl⟩
  have hcover : ∀ c : CLVine G, c ∈ vinesV G → c ∉ Mk → IsIngredient G.molecule S c.atoms →
      ∃ u ∈ runs, c.atoms ⊆ u.atoms := by
    intro c hc hcMk hci
    obtain ⟨t, ht, htc⟩ := hmem1 _ hci
    obtain ⟨u, hu, hsub⟩ := hcov t ht ⟨c, hc, hcMk, htc.symm⟩
    exact ⟨u, hu, htc ▸ hsub⟩
  refine ⟨{
    runs := runs
    surv := L.filter (fun t => ¬ UnmMemMK G Mk t)
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
    obtain ⟨cs, hcs1, hcs2⟩ := choose_listMK (P := fun t (c : CLVine G) =>
      c ∈ vinesV G ∧ c ∉ Mk ∧ IsIngredient G.molecule S c.atoms ∧ c.atoms = t.1) R hR
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
    have htg' : ¬ UnmMemMK G Mk t := by simpa using htg
    refine ⟨hvineM t htL, hingr t htL, ?_⟩
    by_cases hex : ∃ c ∈ vinesV G, c.atoms = t.1
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
    by_cases hg : UnmMemMK G Mk t
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
theorem exists_markedGroupUnits {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)}
    (hmk : markedGroup G Mk S) : Nonempty (MarkedGroupUnits G S Mk) := by
  classical
  have hM : G.molecule.IsMolecule := Mole.garden_isMolecule G
  obtain ⟨c, hcMk, hcV, hci⟩ := hmk
  -- the marked ingredient is a survivor of any spine having it as a member
  have hsurv : ∀ L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree),
      (∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L) →
      ∃ t ∈ L, ¬ UnmMemMK G Mk t := by
    intro L hmemb
    obtain ⟨p, q, h | h⟩ := hmemb _ hci <;>
    · refine ⟨_, h, ?_⟩
      rintro ⟨c', -, hc'Mk, hc't⟩
      exact hc'Mk ((clvine_eq_of_atomsMK hc't) ▸ hcMk)
  have hci' := hci
  rcases hci' with ⟨a, b, n, x, y, hB, hI⟩ | ⟨a, b, e, n, x, y, hends, hn2, hBe, hI⟩
  · -- a VC: the spine lives in the garden molecule
    obtain ⟨L, hs⟩ := Spine.of_chain (chainIngredient_spec hI).1
    have hmemb : ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L :=
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
    obtain ⟨L, hs, hlen⟩ := Spine.of_chain_len (chainIngredient_spec hI).1
    have hlen2 : 2 ≤ L.length := hlen ▸ hn2
    have hmemb : ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L :=
      fun T hT => isIngredient_hvc hM hends hBe hs hlen2 hT
    refine markedGroupUnits_of_spineMK hN hs hBe
      (fun X x y _ hX h => (block_transfer G.molecule hends hX x y).mp h) ?_ ?_ hmemb (hsurv L hmemb)
    · intro ⟨T, p, q⟩ ht
      exact (vine_transfer G.molecule hends (hs.not_both hlen2 ht) p q).mp (hs.mem_vine ht).1
    · intro ⟨T, p, q⟩ ht
      exact Or.inr ⟨a, b, e, L.length, p, q, hends, hlen2, hBe, hs.ingredient_of_mem ht⟩

end WaveTurbulence.RedSplice
