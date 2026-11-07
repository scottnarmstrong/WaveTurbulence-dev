/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLinkParents
import Mathlib.Tactic

/-! # At most two selected links meet each atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appbRungInterval_mem_index {m : ℕ} {u v : Fin (m+1) → V}
    (hinj : Function.Injective (Sum.elim u v)) (j : Fin (m+1)) (i : Fin m) :
    u j ∈ appbRungInterval u v i → i.val = j.val ∨ i.val+1 = j.val := by
  obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hinj
  simp only [appbRungInterval,mem_insert,mem_singleton]
  rintro (h | h | h | h)
  · exact Or.inl (congrArg Fin.val (hu h)).symm
  · exact Or.inr (congrArg Fin.val (hu h)).symm
  · exact False.elim (hcross j i.castSucc h)
  · exact False.elim (hcross j i.succ h)

theorem appbRungInterval_through_card {m : ℕ} {u v : Fin (m+1) → V}
    (hinj : Function.Injective (Sum.elim u v)) (x : V) :
    ((univ : Finset (Fin m)).filter (fun i => x ∈ appbRungInterval u v i)).card ≤ 2 := by
  classical
  by_cases hx : x ∈ Molecule.ladderAtoms u v
  · have hidx : ∃ j : Fin (m+1), ∀ i : Fin m,
        x ∈ appbRungInterval u v i → i.val = j.val ∨ i.val+1 = j.val := by
      rcases mem_union.mp hx with hx | hx
      · obtain ⟨j,_,rfl⟩ := mem_image.mp hx
        exact ⟨j,appbRungInterval_mem_index hinj j⟩
      · obtain ⟨j,_,rfl⟩ := mem_image.mp hx
        have hswap : Function.Injective (Sum.elim v u) := by
          obtain ⟨hu,hv,hcross⟩ := Sum.elim_injective.mp hinj
          exact Sum.elim_injective.mpr ⟨hv,hu,fun a b h => hcross b a h.symm⟩
        refine ⟨j,fun i hi => appbRungInterval_mem_index hswap j i ?_⟩
        simpa only [appbRungInterval,mem_insert,mem_singleton,or_assoc,or_comm,or_left_comm] using hi
    obtain ⟨j,hj⟩ := hidx
    let s := (univ : Finset (Fin m)).filter (fun i => x ∈ appbRungInterval u v i)
    have hsub : s.image Fin.val ⊆ {j.val,j.val-1} := by
      intro k hk
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
      rcases hj i (mem_filter.mp hi).2 with h | h
      · simp [h]
      · have he : i.val = j.val-1 := by omega
        simp [he]
    calc
      s.card = (s.image Fin.val).card := (card_image_of_injective s Fin.val_injective).symm
      _ ≤ ({j.val,j.val-1} : Finset ℕ).card := card_le_card hsub
      _ ≤ 2 := card_le_two
  · have he : ((univ : Finset (Fin m)).filter (fun i => x ∈ appbRungInterval u v i)) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro i hi hmem
      apply hx
      simp only [appbRungInterval,mem_insert,mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      all_goals simp [Molecule.ladderAtoms]
    rw [he,card_empty]
    omega

/-- DH23 ladder bookkeeping: at most two source links contain any atom. -/
theorem appbLinks_through_card (M : Molecule V D) (hM : M.IsMolecule) (x : V) :
    ((appbLinks M).filter (fun S => x ∈ S)).card ≤ 2 := by
  classical
  let A := (appbLinks M).filter (fun S => x ∈ S)
  by_cases hn : A.Nonempty
  · obtain ⟨S,hS⟩ := hn
    have hlink := (mem_appbLinks M S).mp (mem_filter.mp hS).1
    let T := appbLinkParent M S
    have hT := (appbLinkParent_spec hlink).1
    have hxT : x ∈ T := (appbLinkParent_spec hlink).2 (mem_filter.mp hS).2
    obtain ⟨m,u,v,hL,hTV⟩ := (mem_filter.mp hT).2.1
    have hsub : A ⊆ ((univ : Finset (Fin m)).filter
        (fun i => x ∈ appbRungInterval u v i)).image (appbRungInterval u v) := by
      intro U hU
      have hUL := (mem_appbLinks M U).mp (mem_filter.mp hU).1
      have hxU := (mem_filter.mp hU).2
      have hUT : U ⊆ T := by
        obtain ⟨p,q,hPQ,hUV⟩ := hUL
        rw [← hUV]
        exact Degen.sourceLadder_subset_maximal_of_intersects M
          (fun _ ha => deg_le_four M hM ha) hT hPQ ⟨x,hxT,by rw [hUV]; exact hxU⟩
      obtain ⟨i,hi⟩ := hUL.eq_rungInterval hM hL (by rw [hTV]; exact hUT)
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,by rw [← hi]; exact hxU⟩,hi.symm⟩
    exact (card_le_card hsub).trans ((card_image_le).trans (appbRungInterval_through_card hL.2.1 x))
  · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hn
    change A.card ≤ 2
    rw [he,card_empty]
    omega

end WaveTurbulence.Mole
