/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.A.VineSurvChainMK2
import Mathlib.Tactic

/-!
# B2c MK-SUBPRO: chain order and pairwise meeting of the survivor objects of `G_sb`

For the list `survObjs G σ Mk` (the world's `SurvivorData.surv`, ruling R169 and C0 finding F-C0-5):

* `survObjs_chainOrder`: survivor objects that meet have consecutive indices (`SurvChainOrder`);
* `survObjs_inter_card`: two distinct survivor objects share at most one atom (`Structural`, third conjunct).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.Mole TTree WaveTurbulence.Stage1
  WaveTurbulence.LGSpine

variable {w : ℕ} {G : Garden w}

theorem groupSurvMk_eq_units {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)} (h : markedGroup G Mk S) :
    groupSurvMk G Mk S = (markedUnitsOfMK h).surv :=
  groupSurvMk_of_marked h (exists_markedGroupUnits h)

theorem marked_of_mem_groupSurvMk {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ groupSurvMk G Mk S) :
    markedGroup G Mk S := by
  by_contra hm
  rw [groupSurvMk_of_not_marked hm] at ht
  cases ht

theorem mem_survivorsMk_iff' {σ : Prescription G} {Mk : Set (CLVine G)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} :
    t ∈ survivorsMk G σ Mk ↔ ∃ S ∈ sgGroups G σ, t ∈ groupSurvMk G Mk S := by
  rw [survivorsMk_eq, List.mem_flatMap]

theorem sgGroups_nodup (G : Garden w) (σ : Prescription G) : (sgGroups G σ).Nodup := by
  classical
  unfold sgGroups
  exact (Finset.nodup_toList _).filter _

/-- A survivor of a group lies in the group. -/
theorem groupSurvMk_sub {Mk : Set (CLVine G)} {S : Finset (GBranch G.tree)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (ht : t ∈ groupSurvMk G Mk S) :
    t.1 ⊆ S ∧ t.2.1 ∈ t.1 := by
  have hm := marked_of_mem_groupSurvMk ht
  rw [groupSurvMk_eq_units hm] at ht
  obtain ⟨⟨X, hX⟩, hI, -⟩ := (markedUnitsOfMK hm).surv_spec t ht
  exact ⟨isIngredient_subset hI, hX.1.2.1⟩

theorem groupSurvMk_nodup {Mk : Set (CLVine G)} (S : Finset (GBranch G.tree)) : (groupSurvMk G Mk S).Nodup := by
  by_cases hm : markedGroup G Mk S
  · rw [groupSurvMk_eq_units hm]
    obtain ⟨D', _, _, N, L, a, b, -, hs, -, -, -, -, -, hsub, -⟩ := (markedUnitsOfMK hm).surv_spine
    exact hsub.nodup hs.nodupMK
  · rw [groupSurvMk_of_not_marked hm]
    exact List.nodup_nil

section main
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
include hM

theorem survivorsMk_nodup : (survivorsMk G σ Mk).Nodup := by
  rw [survivorsMk_eq, List.nodup_flatMap]
  refine ⟨fun S _ => groupSurvMk_nodup S, (sgGroups_nodup G σ).pairwise_of_forall_ne ?_⟩
  intro S hS S' hS' hne t ht ht'
  obtain ⟨hsub, hj⟩ := groupSurvMk_sub ht
  obtain ⟨hsub', -⟩ := groupSurvMk_sub ht'
  exact Finset.disjoint_left.mp (groups_disjoint hM (mem_sgGroups.mp hS).1 (mem_sgGroups.mp hS').1 hne)
    (hsub hj) (hsub' hj)

/-- **Survivors whose images meet are neighbours in `survivorsMk`.** -/
theorem survivorsMk_meet_consecutive {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ survivorsMk G σ Mk) (ht' : t' ∈ survivorsMk G σ Mk) (hne : t ≠ t')
    {z z' : GBranch G.tree} (hz : z ∈ t.1) (hz' : z' ∈ t'.1)
    (he : (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z = (stSt G σ Mk).M.pi (stSt G σ Mk).hcls z') :
    (∃ A B, survivorsMk G σ Mk = A ++ t :: t' :: B) ∨ ∃ A B, survivorsMk G σ Mk = A ++ t' :: t :: B := by
  obtain ⟨S, hS, htS⟩ := mem_survivorsMk_iff'.mp ht
  obtain ⟨S', hS', htS'⟩ := mem_survivorsMk_iff'.mp ht'
  have hSS : S = S' := group_eq_of_pi_eq hM σ (mem_sgGroups.mp hS).1 (mem_sgGroups.mp hS').1
    ((groupSurvMk_sub htS).1 hz) ((groupSurvMk_sub htS').1 hz') he
  subst hSS
  have hm := marked_of_mem_groupSurvMk htS
  have hσ := (mem_sgGroups.mp hS).2
  have hg := groupSurvMk_eq_units hm
  rw [hg] at htS htS'
  obtain ⟨G1, G2, hsg⟩ := List.append_of_mem hS
  have hsplit : survivorsMk G σ Mk = (G1.flatMap (groupSurvMk G Mk)) ++ (groupSurvMk G Mk S ++
      G2.flatMap (groupSurvMk G Mk)) := by
    rw [survivorsMk_eq, hsg, List.flatMap_append, List.flatMap_cons]
  rcases group_meet_consecutive hM σ (mem_sgGroups.mp hS).1 hσ hm htS htS' hne hz hz' he with
    ⟨A, B, hAB⟩ | ⟨A, B, hAB⟩
  · refine Or.inl ⟨G1.flatMap (groupSurvMk G Mk) ++ A, B ++ G2.flatMap (groupSurvMk G Mk), ?_⟩
    rw [hsplit, hg, hAB]; simp
  · refine Or.inr ⟨G1.flatMap (groupSurvMk G Mk) ++ A, B ++ G2.flatMap (groupSurvMk G Mk), ?_⟩
    rw [hsplit, hg, hAB]; simp

/-- **Two distinct survivors share at most one atom of `G_sb`.** -/
theorem survivorsMk_inter_card {t t' : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree}
    (ht : t ∈ survivorsMk G σ Mk) (ht' : t' ∈ survivorsMk G σ Mk) (hne : t ≠ t') :
    (t.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∩
      t'.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls)).card ≤ 1 := by
  classical
  obtain ⟨S, hS, htS⟩ := mem_survivorsMk_iff'.mp ht
  obtain ⟨S', hS', htS'⟩ := mem_survivorsMk_iff'.mp ht'
  by_cases hSS : S = S'
  · subst hSS
    have hm := marked_of_mem_groupSurvMk htS
    rw [groupSurvMk_eq_units hm] at htS htS'
    exact group_inter_card hM σ (mem_sgGroups.mp hS).1 (mem_sgGroups.mp hS).2 hm htS htS' hne
  · have hd : (t.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls) ∩
        t'.1.image ((stSt G σ Mk).M.pi (stSt G σ Mk).hcls)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      obtain ⟨hc1, hc2⟩ := Finset.mem_inter.mp hc
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc1
      obtain ⟨z', hz', he⟩ := Finset.mem_image.mp hc2
      exact hSS (group_eq_of_pi_eq hM σ (mem_sgGroups.mp hS).1 (mem_sgGroups.mp hS').1
        ((groupSurvMk_sub htS).1 hz) ((groupSurvMk_sub htS').1 hz') he.symm)
    rw [hd]; simp

end main

/-- In a list without duplicates, the positions of two neighbours differ by one. -/
theorem nodup_neighbor_index {α : Type*} {l A B : List α} {x y : α} (hnd : l.Nodup) (hl : l = A ++ x :: y :: B)
    (i j : Fin l.length) (hi : l.get i = x) (hj : l.get j = y) : j.val = i.val + 1 := by
  have hlen : A.length + 1 < l.length := by rw [hl]; simp
  have hx : l.get ⟨A.length, by omega⟩ = x := by subst hl; simp
  have hy : l.get ⟨A.length + 1, hlen⟩ = y := by subst hl; simp
  have h1 : i = ⟨A.length, by omega⟩ := (List.Nodup.get_inj_iff hnd).mp (hi.trans hx.symm)
  have h2 : j = ⟨A.length + 1, hlen⟩ := (List.Nodup.get_inj_iff hnd).mp (hj.trans hy.symm)
  rw [h1, h2]

theorem survObjs_get {σ : Prescription G} {Mk : Set (CLVine G)} (i : Fin (survObjs G σ Mk).length) :
    ∃ (j : Fin (survivorsMk G σ Mk).length) (hj : (survivorsMk G σ Mk).get j ∈ survivorsMk G σ Mk),
      j.val = i.val ∧ (survObjs G σ Mk).get i = survObj hj := by
  refine ⟨⟨i.val, by simpa [survObjs] using i.2⟩, List.get_mem _ _, rfl, ?_⟩
  rw [List.get_eq_getElem]
  simp only [survObjs, List.getElem_map, List.getElem_attach, List.get_eq_getElem]

section main2
variable (hM : G.molecule.IsMolecule) (σ : Prescription G) {Mk : Set (CLVine G)}
include hM

/-- **The chain order of the survivor objects** (`SurvChainOrder`, C0 finding F-C0-5). -/
theorem survObjs_chainOrder (i j : Fin (survObjs G σ Mk).length) (hij : i ≠ j)
    (hm : ¬ Disjoint ((survObjs G σ Mk).get i).atoms ((survObjs G σ Mk).get j).atoms) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  obtain ⟨i', hi', hii, hgi⟩ := survObjs_get i
  obtain ⟨j', hj', hjj, hgj⟩ := survObjs_get j
  rw [hgi, hgj, (survObj_spec hi').1, (survObj_spec hj').1] at hm
  obtain ⟨c, hc1, hc2⟩ := Finset.not_disjoint_iff.mp hm
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc1
  obtain ⟨z', hz', he⟩ := Finset.mem_image.mp hc2
  have hnd := survivorsMk_nodup hM σ (Mk := Mk)
  have hne : (survivorsMk G σ Mk).get i' ≠ (survivorsMk G σ Mk).get j' := by
    intro e
    have := (List.Nodup.get_inj_iff hnd).mp e
    exact hij (Fin.ext (by rw [← hii, ← hjj, this]))
  rcases survivorsMk_meet_consecutive hM σ hi' hj' hne hz hz' he.symm with ⟨A, B, hAB⟩ | ⟨A, B, hAB⟩
  · left
    have := nodup_neighbor_index hnd hAB i' j' rfl rfl
    omega
  · right
    have := nodup_neighbor_index hnd hAB j' i' rfl rfl
    omega

/-- **Two distinct survivor objects share at most one atom** (`Structural`, third conjunct). -/
theorem survObjs_inter_card (i j : Fin (survObjs G σ Mk).length) (hij : i ≠ j) :
    (((survObjs G σ Mk).get i).atoms ∩ ((survObjs G σ Mk).get j).atoms).card ≤ 1 := by
  obtain ⟨i', hi', hii, hgi⟩ := survObjs_get i
  obtain ⟨j', hj', hjj, hgj⟩ := survObjs_get j
  rw [hgi, hgj, (survObj_spec hi').1, (survObj_spec hj').1]
  have hnd := survivorsMk_nodup hM σ (Mk := Mk)
  have hne : (survivorsMk G σ Mk).get i' ≠ (survivorsMk G σ Mk).get j' := by
    intro e
    have := (List.Nodup.get_inj_iff hnd).mp e
    exact hij (Fin.ext (by rw [← hii, ← hjj, this]))
  exact survivorsMk_inter_card hM σ hi' hj' hne

end main2

end WaveTurbulence.VineA.NormalizedSplice
