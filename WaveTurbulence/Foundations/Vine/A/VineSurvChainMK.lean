/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineSurvMK
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: survivors of one chain meet only as neighbours (o75 Lemma 3(ii), §4.6 chain order)

For a marked SG group `S` with runs and survivors `U = markedUnitsOfMK h`, and any spine `L` of the group whose
members not in runs are exactly the survivors (`MarkedGroupUnits.surv_spine`):

* `run_of_pi_eq`: two distinct atoms of `S` with the same image in `G_sb` lie in one run;
* `common_joint`: an atom of a survivor `x` whose image is also the image of an atom of another member is a joint of
  `x` (interior atoms of survivors are unclassified, and distinct members share only joints);
* `right_neighbor` / `left_neighbor`: if the image of the lower (upper) joint of a survivor `x` is the image of an
  atom of another survivor `y`, then `y` follows (precedes) `x` in the spine with only run members between them.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine

variable {w : ℕ} {G : Garden w}

section group
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
include hM

/-- An atom classified by the splice state lies in a unit of `unitBlocks`. -/
theorem unit_of_cls {z : GBranch G.tree} (hz : (stSt G σ Mk).cls z ≠ none) :
    ∃ u ∈ unitBlocks G σ Mk, z ∈ u.atoms := by
  by_contra hno
  push Not at hno
  exact hz (stSt_cls_noneMk hM σ Mk hno)

/-- **Distinct atoms with one image lie in one run.** -/
theorem run_of_pi_eq {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (h : markedGroup G Mk S)
    {z z' : GBranch G.tree} (hz : z ∈ S) (hne : z ≠ z')
    (he : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z') :
    ∃ u ∈ (markedUnitsOfMK h).runs, z ∈ u.atoms ∧ z' ∈ u.atoms := by
  classical
  have hrep := repC_eq_of_pi_eq hM σ he
  -- a classified atom has the crown of its unit as representative; the crown lies in the unit
  have crown : ∀ x (u : CLBlock G), u ∈ unitBlocks G σ Mk → x ∈ u.atoms → repC (stSt G σ Mk).cls x = u.upper := by
    intro x u hu hx
    simp [repC, stSt_cls_memMk hM σ Mk hu hx]
  have none_ne_crown : ∀ x (u : CLBlock G), u ∈ unitBlocks G σ Mk → (stSt G σ Mk).cls x = none → x ≠ u.upper := by
    intro x u hu hx hxu
    rw [hxu, stSt_cls_memMk hM σ Mk hu u.isBlock.2.1] at hx
    cases hx
  by_cases hcz : (stSt G σ Mk).cls z = none
  · exfalso
    by_cases hcz' : (stSt G σ Mk).cls z' = none
    · apply hne
      simpa [repC, hcz, hcz'] using hrep
    · obtain ⟨u', hu', hzu'⟩ := unit_of_cls hM σ hcz'
      have h1 : repC (stSt G σ Mk).cls z = z := by simp [repC, hcz]
      rw [h1, crown z' u' hu' hzu'] at hrep
      exact none_ne_crown z u' hu' hcz hrep
  · obtain ⟨u, hu, hzu⟩ := unit_of_cls hM σ hcz
    have hcz' : (stSt G σ Mk).cls z' ≠ none := by
      intro hcz'
      have h1 : repC (stSt G σ Mk).cls z' = z' := by simp [repC, hcz']
      rw [h1, crown z u hu hzu] at hrep
      exact none_ne_crown z' u hu hcz' hrep.symm
    obtain ⟨u', hu', hzu'⟩ := unit_of_cls hM σ hcz'
    have hup : u.upper = u'.upper := by rw [← crown z u hu hzu, ← crown z' u' hu' hzu', hrep]
    have huu : u = u' := by
      by_contra hne'
      have hdj := pairwise_symm_forallMK (fun x y h => Disjoint.symm h) (unitBlocks_pairwiseMk hM σ Mk) hu hu' hne'
      exact Finset.disjoint_left.mp hdj u.isBlock.2.1 (hup ▸ u'.isBlock.2.1)
    subst huu
    obtain ⟨S'', hS'', -, hmem⟩ := (mem_unitBlocksMk (Mk := Mk)).mp hu
    have hSS : S = S'' := by
      by_contra hne''
      exact Finset.disjoint_left.mp (groups_disjoint hM hS hS'' hne'') hz (groupUnitsMk_sub hmem hzu)
    subst hSS
    rw [groupUnitsMk_of_markedMK h] at hmem
    exact ⟨u, hmem, hzu, hzu'⟩

variable {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  (h : markedGroup G Mk S) {D' : Type} [Fintype D'] [DecidableEq D'] {N : Molecule (GBranch G.tree) D'}
  {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)} {a b : GBranch G.tree}
  (hs : Spine N L S a b) (hvineM : ∀ t ∈ L, Vine.IsSomeVine G.molecule t.1 t.2.1 t.2.2)
  (hingr : ∀ t ∈ L, IsIngredient G.molecule S t.1)
  (hmemb : ∀ T, IsIngredient G.molecule S T → ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L)
  (hsurvL : ∀ t ∈ L, (t ∈ (markedUnitsOfMK h).surv ↔ ¬ UnmMemMK G Mk t))
include hS hσ hs hvineM hingr hmemb hsurvL

/-- **A common image atom is a joint of the survivor.** -/
theorem common_joint {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (markedUnitsOfMK h).surv) (hxL : x ∈ L) (hyL : y ∈ L) (hxy : x ≠ y)
    {z z' : GBranch G.tree} (hz : z ∈ x.1) (hz' : z' ∈ y.1)
    (he : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z') :
    z = x.2.1 ∨ z = x.2.2 := by
  classical
  by_contra hzj
  push Not at hzj
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := survivor_imageMK hS hσ h hx
  have hcz := hint z hz hzj.1 hzj.2
  by_cases hzz : z = z'
  · subst hzz
    obtain ⟨P0, Q0, hL⟩ := List.append_of_mem hxL
    rw [hL] at hyL hs
    rcases List.mem_append.mp hyL with hyP | hyQ
    · exact hzj.1 (hs.joint_leftMK hyP hz' hz)
    · rcases List.mem_cons.mp hyQ with hyx | hyQ
      · exact hxy hyx.symm
      · exact hzj.2 (hs.joint_rightMK hyQ hz' hz)
  · have hzS : z ∈ S := isIngredient_subset (hingr x hxL) hz
    obtain ⟨u, hu, hzu, -⟩ := run_of_pi_eq hM σ hS h hzS hzz he
    have hub : u ∈ unitBlocks G σ Mk := (mem_unitBlocksMk (Mk := Mk)).mpr
      ⟨S, hS, hσ, by rw [groupUnitsMk_of_markedMK h]; exact hu⟩
    rw [stSt_cls_memMk hM σ Mk hub hzu] at hcz
    cases hcz

/-- **The right neighbour.** If the image of the lower joint of a survivor `x` is the image of an atom of another
survivor `y`, then `y` follows `x` in the spine, with only run members between them. -/
theorem right_neighbor {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (markedUnitsOfMK h).surv) (hxL : x ∈ L) (hy : y ∈ (markedUnitsOfMK h).surv) (hyL : y ∈ L)
    (hxy : x ≠ y) {w' : GBranch G.tree} (hw' : w' ∈ y.1)
    (he : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls x.2.2 = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls w') :
    ∃ P R Q, L = P ++ x :: (R ++ y :: Q) ∧ ∀ r ∈ R, UnmMemMK G Mk r := by
  classical
  obtain ⟨X, hX⟩ := hvineM x hxL
  have hxj : x.2.2 ∈ x.1 := hX.1.2.2.1
  have hxne : x.2.1 ≠ x.2.2 := hX.1.2.2.2.1
  obtain ⟨P0, Q0, hL⟩ := List.append_of_mem hxL
  have hs0 := hs
  rw [hL] at hs0
  have hyPQ : y ∈ P0 ∨ y ∈ Q0 := by
    rw [hL] at hyL
    rcases List.mem_append.mp hyL with h1 | h1
    · exact Or.inl h1
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact absurd h2.symm hxy
      · exact Or.inr h2
  have hxs : ¬ UnmMemMK G Mk x := (hsurvL x hxL).mp hx
  have hys : ¬ UnmMemMK G Mk y := (hsurvL y hyL).mp hy
  by_cases hww : x.2.2 = w'
  · subst hww
    rcases hyPQ with hyP | hyQ
    · exact absurd (hs0.joint_leftMK hyP hw' hxj).symm hxne
    · cases Q0 with
      | nil => cases hyQ
      | cons q Q1 =>
        rcases List.mem_cons.mp hyQ with hyq | hyQ1
        · subst hyq
          exact ⟨P0, [], Q1, hL, fun r hr => by cases hr⟩
        · exfalso
          have hs1 : Spine N ((P0 ++ [x]) ++ q :: Q1) S a b := by simpa using hs0
          exact Finset.disjoint_left.mp (hs1.sepMK (by simp) hyQ1) hxj hw'
  · have hzS : x.2.2 ∈ S := isIngredient_subset (hingr x hxL) hxj
    obtain ⟨u, hu, hzu, hwu⟩ := run_of_pi_eq hM σ hS h hzS hww he
    obtain ⟨Pu, Ru, Qu, hLu, -, hunm, hat, -, -⟩ :=
      (markedUnitsOfMK h).run_canonMK hs (fun t ht => hvineM t ht) hingr hmemb hu
    have hxR : x ∉ Ru := fun hxR => hxs (hunm x hxR)
    obtain ⟨r, hr, hxr⟩ := (hat _).mp hzu
    obtain ⟨hQ0, -⟩ := run_adj_rightMK hs (fun t ht => hvineM t ht) hL hLu hxR hr hxr
    obtain ⟨r', hr', hwr'⟩ := (hat _).mp hwu
    rw [hQ0] at hs0 hyPQ
    rcases hyPQ with hyP | hyQ
    · exfalso
      exact Finset.disjoint_left.mp (hs0.sepMK hyP (List.mem_append_left _ hr')) hw' hwr'
    · rcases List.mem_append.mp hyQ with hyR | hyQu
      · exact absurd (hunm y hyR) hys
      · cases Qu with
        | nil => cases hyQu
        | cons q Q1 =>
          rcases List.mem_cons.mp hyQu with hyq | hyQ1
          · subst hyq
            exact ⟨P0, Ru, Q1, by rw [hL, hQ0], hunm⟩
          · exfalso
            have hs1 : Spine N ((P0 ++ x :: Ru) ++ q :: Q1) S a b := by simpa using hs0
            exact Finset.disjoint_left.mp (hs1.sepMK (by simp [hr']) hyQ1) hwr' hw'

/-- **The left neighbour.** -/
theorem left_neighbor {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (markedUnitsOfMK h).surv) (hxL : x ∈ L) (hy : y ∈ (markedUnitsOfMK h).surv) (hyL : y ∈ L)
    (hxy : x ≠ y) {w' : GBranch G.tree} (hw' : w' ∈ y.1)
    (he : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls x.2.1 = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls w') :
    ∃ P R Q, L = P ++ y :: (R ++ x :: Q) ∧ ∀ r ∈ R, UnmMemMK G Mk r := by
  classical
  obtain ⟨X, hX⟩ := hvineM x hxL
  have hxj : x.2.1 ∈ x.1 := hX.1.2.1
  have hxne : x.2.1 ≠ x.2.2 := hX.1.2.2.2.1
  obtain ⟨P0, Q0, hL⟩ := List.append_of_mem hxL
  have hs0 := hs
  rw [hL] at hs0
  have hyPQ : y ∈ P0 ∨ y ∈ Q0 := by
    rw [hL] at hyL
    rcases List.mem_append.mp hyL with h1 | h1
    · exact Or.inl h1
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact absurd h2.symm hxy
      · exact Or.inr h2
  have hxs : ¬ UnmMemMK G Mk x := (hsurvL x hxL).mp hx
  have hys : ¬ UnmMemMK G Mk y := (hsurvL y hyL).mp hy
  by_cases hww : x.2.1 = w'
  · subst hww
    rcases hyPQ with hyP | hyQ
    · obtain ⟨A, B, hP0⟩ := List.append_of_mem hyP
      cases B.eq_nil_or_concat with
      | inl hB =>
        subst hB
        exact ⟨A, [], Q0, by rw [hL, hP0]; simp, fun r hr => by cases hr⟩
      | inr hB =>
        obtain ⟨B1, q, rfl⟩ := hB
        exfalso
        have hs1 : Spine N ((A ++ y :: B1) ++ q :: (x :: Q0)) S a b := by rw [hP0] at hs0; simpa using hs0
        exact Finset.disjoint_left.mp (hs1.sepMK (by simp) (by simp)) hw' hxj
    · exact (hxne (hs0.joint_rightMK hyQ hw' hxj)).elim
  · have hzS : x.2.1 ∈ S := isIngredient_subset (hingr x hxL) hxj
    obtain ⟨u, hu, hzu, hwu⟩ := run_of_pi_eq hM σ hS h hzS hww he
    obtain ⟨Pu, Ru, Qu, hLu, -, hunm, hat, -, -⟩ :=
      (markedUnitsOfMK h).run_canonMK hs (fun t ht => hvineM t ht) hingr hmemb hu
    have hxR : x ∉ Ru := fun hxR => hxs (hunm x hxR)
    obtain ⟨r, hr, hxr⟩ := (hat _).mp hzu
    obtain ⟨hP0, -⟩ := run_adj_leftMK hs (fun t ht => hvineM t ht) hL hLu hxR hr hxr
    obtain ⟨r', hr', hwr'⟩ := (hat _).mp hwu
    rw [hP0] at hs0 hyPQ
    rcases hyPQ with hyP | hyQ
    · rcases List.mem_append.mp hyP with hyPu | hyR
      · obtain ⟨A, B, hPu⟩ := List.append_of_mem hyPu
        cases B.eq_nil_or_concat with
        | inl hB =>
          subst hB
          exact ⟨A, Ru, Q0, by rw [hL, hP0, hPu]; simp, hunm⟩
        | inr hB =>
          obtain ⟨B1, q, rfl⟩ := hB
          exfalso
          have hs1 : Spine N ((A ++ y :: B1) ++ q :: (Ru ++ x :: Q0)) S a b := by rw [hPu] at hs0; simpa using hs0
          exact Finset.disjoint_left.mp (hs1.sepMK (by simp) (by simp [hr'])) hw' hwr'
      · exact absurd (hunm y hyR) hys
    · exfalso
      exact Finset.disjoint_left.mp (hs0.sepMK (List.mem_append_right _ hr') hyQ) hwr' hw'

end group

end WaveTurbulence.VineA.NormalizedSplice
