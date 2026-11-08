/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: the chain order of the survivors (o75 §4.6, Theorem 7.5′(2); C0 finding F-C0-5)

* `group_meet_consecutive`: two survivors of one marked group whose images in `G_sb` meet are consecutive in the
  group's survivor list;
* `group_inter_card`: two distinct survivors of one group share at most one atom of `G_sb`;
* `survivorsMk_nodup`, `survivorsMk_meet_consecutive`: the same across the whole list `survivorsMk G σ Mk`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine

/-- A sublist of a list without duplicates, whose members are exactly the members satisfying `p`, is the filter. -/
theorem sublist_eq_filter {α : Type*} (p : α → Prop) [DecidablePred p] {l l' : List α} (hsub : l'.Sublist l)
    (hnd : l.Nodup) (hmem : ∀ x ∈ l, (x ∈ l' ↔ p x)) : l' = l.filter (fun x => decide (p x)) := by
  induction hsub with
  | slnil => rfl
  | @cons l1 l2 a h ih =>
    have ha : a ∉ l2 := (List.nodup_cons.mp hnd).1
    have hpa : ¬ p a := fun hp => ha (h.subset ((hmem a (List.mem_cons_self)).mpr hp))
    rw [List.filter_cons_of_neg (by simpa using hpa)]
    exact ih (List.nodup_cons.mp hnd).2 (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
  | @cons_cons l1 l2 a h ih =>
    have ha : a ∉ l2 := (List.nodup_cons.mp hnd).1
    have hpa : p a := (hmem a List.mem_cons_self).mp List.mem_cons_self
    rw [List.filter_cons_of_pos (by simpa using hpa)]
    congr 1
    refine ih (List.nodup_cons.mp hnd).2 (fun x hx => ?_)
    have hxa : x ≠ a := fun e => ha (e ▸ hx)
    rw [← hmem x (List.mem_cons_of_mem _ hx)]
    simp [hxa]

variable {w : ℕ} {G : Garden w}

section group
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
  {S : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (hσ : σ S = Molecule.GapKind.SG)
  (h : markedGroup G Mk S)
include hM hS hσ

/-- **Survivors whose images meet are neighbours in the survivor list of their group.** -/
theorem group_meet_consecutive {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (markedUnitsOfMK h).surv) (hy : y ∈ (markedUnitsOfMK h).surv) (hxy : x ≠ y)
    {z z' : GBranch G.tree} (hz : z ∈ x.1) (hz' : z' ∈ y.1)
    (he : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z') :
    (∃ A B, (markedUnitsOfMK h).surv = A ++ x :: y :: B) ∨ ∃ A B, (markedUnitsOfMK h).surv = A ++ y :: x :: B := by
  classical
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hvineM, hingr, hmemb, hsub, hmem⟩ := (markedUnitsOfMK h).surv_spine
  have hsurvL : ∀ t ∈ L, (t ∈ (markedUnitsOfMK h).surv ↔ ¬ UnmMemMK G Mk t) := hmem
  have hfil := sublist_eq_filter (fun t => ¬ UnmMemMK G Mk t) hsub hs.nodupMK hsurvL
  have hxL := hsub.subset hx
  have hyL := hsub.subset hy
  have hxp : ¬ UnmMemMK G Mk x := (hsurvL x hxL).mp hx
  have hyp : ¬ UnmMemMK G Mk y := (hsurvL y hyL).mp hy
  rcases common_joint hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hyL hxy hz hz' he with rfl | rfl
  · obtain ⟨P, R, Q, hL, hR⟩ := left_neighbor hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hy hyL hxy hz' he
    have hRf : R.filter (fun t => decide (¬ UnmMemMK G Mk t)) = [] :=
      List.filter_eq_nil_iff.mpr (fun r hr => by simpa using hR r hr)
    refine Or.inr ⟨P.filter (fun t => decide (¬ UnmMemMK G Mk t)), Q.filter (fun t => decide (¬ UnmMemMK G Mk t)), ?_⟩
    rw [hfil, hL, List.filter_append, List.filter_cons_of_pos (by simpa using hyp), List.filter_append, hRf,
      List.filter_cons_of_pos (by simpa using hxp)]
    rfl
  · obtain ⟨P, R, Q, hL, hR⟩ := right_neighbor hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hy hyL hxy hz' he
    have hRf : R.filter (fun t => decide (¬ UnmMemMK G Mk t)) = [] :=
      List.filter_eq_nil_iff.mpr (fun r hr => by simpa using hR r hr)
    refine Or.inl ⟨P.filter (fun t => decide (¬ UnmMemMK G Mk t)), Q.filter (fun t => decide (¬ UnmMemMK G Mk t)), ?_⟩
    rw [hfil, hL, List.filter_append, List.filter_cons_of_pos (by simpa using hxp), List.filter_append, hRf,
      List.filter_cons_of_pos (by simpa using hyp)]
    rfl

/-- **Two distinct survivors of one group share at most one atom of `G_sb`.** -/
theorem group_inter_card {x y : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (hx : x ∈ (markedUnitsOfMK h).surv) (hy : y ∈ (markedUnitsOfMK h).surv) (hxy : x ≠ y) :
    (x.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∩ y.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls)).card
      ≤ 1 := by
  classical
  obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, hvineM, hingr, hmemb, hsub, hmem⟩ := (markedUnitsOfMK h).surv_spine
  have hsurvL : ∀ t ∈ L, (t ∈ (markedUnitsOfMK h).surv ↔ ¬ UnmMemMK G Mk t) := hmem
  have hxL := hsub.subset hx
  have hyL := hsub.subset hy
  rw [Finset.card_le_one]
  intro c1 hc1 c2 hc2
  obtain ⟨hc1x, hc1y⟩ := Finset.mem_inter.mp hc1
  obtain ⟨hc2x, hc2y⟩ := Finset.mem_inter.mp hc2
  obtain ⟨z1, hz1, rfl⟩ := Finset.mem_image.mp hc1x
  obtain ⟨w1, hw1, he1⟩ := Finset.mem_image.mp hc1y
  obtain ⟨z2, hz2, rfl⟩ := Finset.mem_image.mp hc2x
  obtain ⟨w2, hw2, he2⟩ := Finset.mem_image.mp hc2y
  have j1 := common_joint hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hyL hxy hz1 hw1 he1.symm
  have j2 := common_joint hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hyL hxy hz2 hw2 he2.symm
  by_cases hzz : z1 = z2
  · rw [hzz]
  · exfalso
    -- both joints of `x` have images in `y`: `y` is both the right and the left neighbour of `x`
    have hboth : (∃ w ∈ y.1, (stSt G σ Mk).M.pi (stSt G σ Mk).hcls x.2.1 = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls w) ∧
        ∃ w ∈ y.1, (stSt G σ Mk).M.pi (stSt G σ Mk).hcls x.2.2 = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls w := by
      rcases j1 with rfl | rfl <;> rcases j2 with rfl | rfl
      · exact absurd rfl hzz
      · exact ⟨⟨w1, hw1, he1.symm⟩, ⟨w2, hw2, he2.symm⟩⟩
      · exact ⟨⟨w2, hw2, he2.symm⟩, ⟨w1, hw1, he1.symm⟩⟩
      · exact absurd rfl hzz
    obtain ⟨⟨u1, hu1, hl⟩, ⟨u2, hu2, hr⟩⟩ := hboth
    obtain ⟨P, R, Q, hL, -⟩ := right_neighbor hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hy hyL hxy hu2 hr
    obtain ⟨P', R', Q', hL', -⟩ := left_neighbor hM σ hS hσ h hs hvineM hingr hmemb hsurvL hx hxL hy hyL hxy hu1 hl
    have hnd := hs.nodupMK
    have e : P ++ x :: (R ++ y :: Q) = (P' ++ y :: R') ++ x :: Q' := by rw [← hL, hL']; simp
    have hnd' : (P ++ x :: (R ++ y :: Q)).Nodup := hL ▸ hnd
    obtain ⟨hP, -⟩ := app_cons_inj_of_nodupMK hnd' e
    have hyP : y ∈ P := by rw [hP]; simp
    have := List.nodup_append.mp hnd'
    exact this.2.2 y hyP y (by simp) rfl

end group

end WaveTurbulence.VineA.NormalizedSplice
