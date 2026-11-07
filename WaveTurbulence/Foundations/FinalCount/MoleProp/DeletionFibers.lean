/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.FreeCount
public import WaveTurbulence.Foundations.Molecule.Degen.Removal
import Mathlib.Tactic

/-! # Exact fixed-deleted-label fibers for DH23 molecule reductions

The transferred source and energy parameters are obtained from a member of
the actual fiber. They are fixed on that fiber. No zero-charge premise is used.
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

abbrev DeletedDart (M : Molecule V D) (Y : Finset V) :=
  {x : D // ¬(M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y)}

def deletedLabels (M : Molecule V D) (Y : Finset V) {K : Type*} (κ : D → K) :
    DeletedDart M Y → K := fun x => κ x.val

/-- The literal projected admissibility, retaining every remaining source
restriction. No conservation condition is inserted in the relaxed problem. -/
def erasedFreeAdmissibility (M : Molecule V D) (Y : Finset V) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (κ' : Degen.RetainedDart M Y → (Fin d → ℤ)) : Prop :=
  ∃ κ, Adm κ ∧ (∀ x, κ (M.mate x) = κ x) ∧ (fun x : Degen.RetainedDart M Y => κ x.val) = κ'

theorem deletion_pair_injective (M : Molecule V D) (Y : Finset V) {K : Type*} :
    Function.Injective (fun κ : D → K =>
      (deletedLabels M Y κ, fun x : Degen.RetainedDart M Y => κ x.val)) := by
  intro κ κ' h
  funext x
  by_cases hx : M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y
  · exact congrFun (congrArg Prod.snd h) ⟨x,hx⟩
  · exact congrFun (congrArg Prod.fst h) ⟨x,hx⟩

theorem residualMomentum_eq_of_deletedLabels_eq (M : Molecule V D) (Y : Finset V)
    {d : ℕ} (L : ℝ) (w : Mom d) (c : V → Mom d)
    {κ κ' : D → (Fin d → ℤ)} (h : deletedLabels M Y κ = deletedLabels M Y κ') :
    Degen.residualMomentum M Y L w c κ = Degen.residualMomentum M Y L w c κ' := by
  funext z
  unfold Degen.residualMomentum
  congr 1
  apply sum_congr rfl
  intro x hx
  have hmate : M.atom (M.mate x) ∈ Y := (mem_filter.mp hx).2
  have hxdel : ¬(M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y) := fun hh => hh.2 hmate
  have he := congrFun h ⟨x,hxdel⟩
  change κ x = κ' x at he
  simp only [Molecule.kvec,he]

theorem residualEnergy_eq_of_deletedLabels_eq (M : Molecule V D) (Y : Finset V)
    {d : ℕ} (L : ℝ) (w : Mom d) (β : V → ℝ)
    {κ κ' : D → (Fin d → ℤ)} (h : deletedLabels M Y κ = deletedLabels M Y κ') :
    Degen.residualEnergy M Y L w β κ = Degen.residualEnergy M Y L w β κ' := by
  funext z
  unfold Degen.residualEnergy
  congr 1
  apply sum_congr rfl
  intro x hx
  have hmate : M.atom (M.mate x) ∈ Y := (mem_filter.mp hx).2
  have hxdel : ¬(M.atom x ∉ Y ∧ M.atom (M.mate x) ∉ Y) := fun hh => hh.2 hmate
  have he := congrFun h ⟨x,hxdel⟩
  change κ x = κ' x at he
  simp only [Molecule.kvec,he]

/-- Actual fixed-label fibers map injectively to a single legitimate
post-removal counting problem in the relaxed supremum. -/
theorem fixed_deleted_fiber_encard_le (M : Molecule V D) (Y : Finset V) {d : ℕ}
    (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hk0 : ∀ x, k0 (M.mate x) = k0 x) (q : DeletedDart M Y → (Fin d → ℤ)) :
    {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧
      Adm κ ∧ deletedLabels M Y κ = q}.encard ≤
      countEFree (Degen.eraseAtoms M Y) L γ δ w (erasedFreeAdmissibility M Y Adm) := by
  classical
  let A := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧
      Adm κ ∧ deletedLabels M Y κ = q}
  by_cases hne : A.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hne
    let c' := Degen.residualMomentum M Y L w c κ0
    let β' := Degen.residualEnergy M Y L w β κ0
    let T := {κ' | (Degen.eraseAtoms M Y).IsDecoration L w c' κ' ∧
      (Degen.eraseAtoms M Y).IsRestricted L γ δ w β' (fun x => k0 x.val) κ' ∧
      erasedFreeAdmissibility M Y Adm κ'}
    let r := fun κ : D → (Fin d → ℤ) => fun x : Degen.RetainedDart M Y => κ x.val
    have hm : Set.MapsTo r A T := by
      intro κ hκ
      have he : deletedLabels M Y κ = deletedLabels M Y κ0 := hκ.2.2.2.trans hκ0.2.2.2.symm
      have hd := Degen.isDecoration_eraseAtoms M Y hκ.1
      have hr := Degen.isRestricted_eraseAtoms M Y hκ.2.1
      rw [residualMomentum_eq_of_deletedLabels_eq M Y L w c he] at hd
      rw [residualEnergy_eq_of_deletedLabels_eq M Y L w β he] at hr
      exact ⟨hd,hr,κ,hκ.2.2.1,hκ.1.1,rfl⟩
    have hi : Set.InjOn r A := by
      intro κ hκ κ' hκ' hr
      apply deletion_pair_injective M Y
      exact Prod.ext (hκ.2.2.2.trans hκ'.2.2.2.symm) hr
    have hcenters : ∀ x : Degen.RetainedDart M Y,
        k0 ((Degen.eraseAtoms M Y).mate x).val = k0 x.val := fun x => hk0 x.val
    exact (Set.encard_le_encard_of_injOn hm hi).trans
      (encard_le_countEFree (Degen.eraseAtoms M Y) L γ δ w _ c' β' (fun x => k0 x.val) hcenters)
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change A.encard ≤ _
    rw [he,Set.encard_empty]
    exact bot_le

/-- Exact finite projection bound. Subsequent local counting lemmas bound
the actual deleted-label image; no estimate is inserted into this identity. -/
theorem encard_le_deletedImage_mul_post (M : Molecule V D) (Y : Finset V) {d : ℕ}
    {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (hk0 : ∀ x, k0 (M.mate x) = k0 x) :
    let A := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}
    A.encard ≤ ((deletedLabels M Y '' A).ncard : ℕ∞) *
      countEFree (Degen.eraseAtoms M Y) L γ δ w (erasedFreeAdmissibility M Y Adm) := by
  classical
  dsimp only
  let A := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hL γ δ w β k0).subset (fun _ h => h.2.1)
  let S := hf.toFinset
  let E := countEFree (Degen.eraseAtoms M Y) L γ δ w (erasedFreeAdmissibility M Y Adm)
  have hE : E ≠ ⊤ := countEFree_ne_top _ hL γ δ w _
  let N := E.toNat
  have hNE : (N : ℕ∞) = E := ENat.natCast_toNat hE
  have hmem (κ) : κ ∈ S ↔ κ ∈ A := hf.mem_toFinset
  have hfib (q : DeletedDart M Y → (Fin d → ℤ)) :
      (S.filter (fun κ => deletedLabels M Y κ = q)).card ≤ N := by
    have hsub : (S.filter (fun κ => deletedLabels M Y κ = q) : Set (D → (Fin d → ℤ))) ⊆
        {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧
          Adm κ ∧ deletedLabels M Y κ = q} := by
      intro κ hk
      obtain ⟨hk,hq⟩ := Finset.mem_filter.mp hk
      have ha := (hmem κ).mp hk
      exact ⟨ha.1,ha.2.1,ha.2.2,hq⟩
    have hh := (Set.encard_mono hsub).trans (fixed_deleted_fiber_encard_le M Y L γ δ w Adm c β k0 hk0 q)
    rw [Set.encard_coe_eq_coe_finsetCard] at hh
    simpa only [ENat.toNat_natCast] using ENat.toNat_le_toNat hh hE
  have hcard : S.card ≤ (S.image (deletedLabels M Y)).card * N := by
    calc
      _ = ∑ q ∈ S.image (deletedLabels M Y), (S.filter (fun κ => deletedLabels M Y κ = q)).card :=
        card_eq_sum_card_image _ S
      _ ≤ ∑ _q ∈ S.image (deletedLabels M Y), N := sum_le_sum (fun q _ => hfib q)
      _ = _ := by simp only [sum_const,nsmul_eq_mul]; rfl
  have hi : (deletedLabels M Y '' A).ncard = (S.image (deletedLabels M Y)).card := by
    have he : deletedLabels M Y '' A = (S.image (deletedLabels M Y) : Set _) := by
      rw [Finset.coe_image,hf.coe_toFinset]
    rw [he,Set.ncard_coe_finset]
  change A.encard ≤ _
  rw [hf.encard_eq_coe_toFinset_card,hi]
  change (S.card : ℕ∞) ≤ ((S.image (deletedLabels M Y)).card : ℕ∞) * E
  rw [← hNE]
  exact_mod_cast hcard

end WaveTurbulence.MoleProp
