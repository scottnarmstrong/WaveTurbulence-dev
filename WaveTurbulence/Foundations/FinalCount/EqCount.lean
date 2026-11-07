/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.EqPost
import Mathlib.Tactic

/-! # Counting through the (Y2) post molecule when the exit labels agree

DH23 L1969 ("`k_{ℓ₁} = k_{ℓ₂}`: replace both bonds by one"). Copy of `TwoExit.countEFree_le_adm` with `g = 0`: the
transport is exact, so no energy windows are needed (MOLEPROP4's factor `5 K²`, `K = 1 + 4|Y|`, is not size independent
and is not allowed here):

`countEFree N ≤ |scaleFamily| · countEFree N[Y] · sup_{P'} countEFree post (lgAdm post η P')`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace EqPost
variable {N : Molecule V D} (T : TwoExit N)

/-- The unit-ball centers of the post molecule (the new bond gets the center of `y`). -/
def centers {d : ℕ} (k0 : D → Mom d) : Degen.RetainedDart N T.Y ⊕ Bool → Mom d :=
  Sum.elim (fun z => k0 z.val) (fun _ => k0 T.y)

/-- **The counting inequality of a two-exit removal with equal exit labels.** -/
theorem countEFree_le_eq
    (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) {d : ℕ} {L γ δ η : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (P : Finset V → ℝ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm N L γ η P κ) (hEq : ∀ κ, Adm κ → (∀ z, κ (N.mate z) = κ z) → κ T.x = κ T.y) :
    MoleProp.countEFree N L γ δ (0 : Mom d) Adm ≤
      ((T.scaleFamily L P).card : ℕ∞) *
        MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) *
        ⨆ P' ∈ T.scaleFamily L P, MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ η P') := by
  classical
  have hLp : 0 < L := by linarith
  set F := MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d)
    (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) with hFdef
  set G := ⨆ P' ∈ T.scaleFamily L P, MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ η P')
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ}
  have hAfin : A.Finite := (Mole.finite_restricted N hLp γ δ 0 β k0).subset fun _ h => h.2.1
  let E : (Finset V → ℝ) → Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) :=
    fun P' => {κ' | T.post.IsDecoration L 0 (T.postCharges c 0) κ' ∧
      T.post.IsRestricted L γ δ 0 β (centers T k0) κ' ∧ lgAdm T.post L γ η P' κ'}
  have hk0' : ∀ z : Degen.RetainedDart N T.Y ⊕ Bool, centers T k0 (T.post.mate z) = centers T k0 z := by
    intro z; rcases z with z | t
    · exact hk0 z.val
    · rfl
  have hE : ∀ P' ∈ T.scaleFamily L P, (E P').encard ≤ G := by
    intro P' hP'
    refine (MoleProp.encard_le_countEFree T.post L γ δ 0 _ (T.postCharges c 0) β (centers T k0) hk0').trans ?_
    exact le_iSup₂_of_le (f := fun P'' _ => MoleProp.countEFree T.post L γ δ (0 : Mom d)
      (lgAdm T.post L γ η P'')) P' hP' le_rfl
  let B : Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) := ⋃ P' ∈ T.scaleFamily L P, E P'
  have hmaps : ∀ κ ∈ A, T.postLabels κ 0 ∈ B := by
    intro κ hκ
    obtain ⟨hdec, hres, hadm⟩ := hκ
    have hxy := hEq κ hadm hdec.1
    obtain ⟨P', hP', hcgr⟩ := T.exists_scaleFamily_cgr hloop hdeg hopen hL hdec.1 (hAdm κ hadm).2 0
    refine Set.mem_biUnion hP' ⟨T.post_isDecoration hdec 0, ⟨?_, ?_⟩, ⟨post_largeGap_eq T hdec.1 hxy (hAdm κ hadm).1, hcgr⟩⟩
    · intro v hv
      rw [T.post_atoms] at hv
      obtain ⟨hvN, hvY⟩ := mem_sdiff.mp hv
      rw [post_gamma_eq T L 0 hdec.1 hxy hvY]
      exact hres.1 v hvN
    · rintro (z | t)
      · exact hres.2 z.val
      · change ‖Molecule.kvec L 0 (T.postLabels κ 0) (Sum.inr t) - k0 T.y‖ ≤ 1
        rw [kvec_new_eq T L 0 t]; exact hres.2 T.y
  have hfib : ∀ κ' ∈ B, {κ | κ ∈ A ∧ T.postLabels κ 0 = κ'}.encard ≤ F := by
    intro κ' _
    by_cases hne : {κ | κ ∈ A ∧ T.postLabels κ 0 = κ'}.Nonempty
    · obtain ⟨κ₀, ⟨hκ₀, hκ₀'⟩⟩ := hne
      refine (Set.encard_mono ?_).trans (MoleProp.fixed_deleted_fiber_encard_le N (N.atoms \ T.Y) L γ δ 0
        Adm c β k0 hk0 (MoleProp.deletedLabels N (N.atoms \ T.Y) κ₀))
      rintro κ ⟨⟨hdec, hres, hadm⟩, hκ'⟩
      refine ⟨hdec, hres, hadm, ?_⟩
      have hpost : T.postLabels κ 0 = T.postLabels κ₀ 0 := hκ'.trans hκ₀'.symm
      have hdec₀ := hκ₀.1
      have hxy := hEq κ hadm hdec.1
      have hxy₀ := hEq κ₀ hκ₀.2.2 hdec₀.1
      have hnew := congrFun hpost (Sum.inr true)
      simp only [TwoExit.postLabels, Sum.elim_inr, zero_smul, add_zero] at hnew
      have hx : κ T.x = κ₀ T.x := hxy.trans (hnew.trans hxy₀.symm)
      funext ⟨z, hz⟩
      simp only [MoleProp.deletedLabels]
      rcases T.dart_cases z with h | h | rfl | rfl | rfl | rfl
      · exfalso; apply hz
        exact ⟨fun h' => (mem_sdiff.mp h').2 h.1, fun h' => (mem_sdiff.mp h').2 h.2⟩
      · exact congrFun hpost (Sum.inl ⟨z, h.1, h.2⟩)
      · exact hx
      · exact hnew
      · rw [hdec.1, hdec₀.1]; exact hx
      · rw [hdec.1, hdec₀.1]; exact hnew
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.encard_empty]; exact bot_le
  have hB : B.encard ≤ ((T.scaleFamily L P).card : ℕ∞) * G := by
    refine (encard_biUnion_le (T.scaleFamily L P) E).trans ?_
    calc ∑ P' ∈ T.scaleFamily L P, (E P').encard ≤ ∑ _P' ∈ T.scaleFamily L P, G := sum_le_sum fun P' hP' => hE P' hP'
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  calc A.encard ≤ B.encard * F := encard_le_mul_of_fiber hAfin (fun κ => T.postLabels κ 0) B hmaps F hfib
    _ ≤ ((T.scaleFamily L P).card : ℕ∞) * G * F := mul_le_mul_left hB F
    _ = _ := by ring

end EqPost
end WaveTurbulence.FinalCountG8
