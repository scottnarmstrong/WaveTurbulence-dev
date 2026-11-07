/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCount
import Mathlib.Tactic

/-! # The (Y2) count for any admissibility below `lgAdm`

As `TwoExit.countEFree_le`, with the decorations of `N` restricted by any `Adm ⊆ lgAdm`; the post decorations are
then restricted to the images (`postAdm`) of `Adm`-decorations under the transport with multiplier `g`. This lets a
condition on post decorations be pulled back to `N` (DH23 Prop 10.4(2): "the exact case may depend on assumptions we
impose on the decoration").
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **The transported admissibility**: post decorations with LG `η'` and cell scales `P'`, images of `Adm`-decorations
under the transport with multiplier `g`. -/
def postAdm {d : ℕ} (Adm : (D → (Fin d → ℤ)) → Prop) (W : ℤ → (D → (Fin d → ℤ)) → Prop) (L γ η' : ℝ)
    (P' : Finset V → ℝ) (g : ℤ) (κ' : Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) : Prop :=
  lgAdm T.post L γ η' P' κ' ∧ ∃ κ, Adm κ ∧ (∀ x, κ (N.mate x) = κ x) ∧ W g κ ∧ T.postLabels κ g = κ'

/-- **The counting inequality of a two-exit (Y2) removal, for any admissibility below `lgAdm`.** -/
theorem countEFree_le_adm
    (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) {d : ℕ} {L γ δ η : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (P : Finset V → ℝ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm N L γ η P κ) (W : ℤ → (D → (Fin d → ℤ)) → Prop)
    (hW : ∀ κ, Adm κ → (∀ x, κ (N.mate x) = κ x) →
      ∃ g ∈ Icc (0 : ℤ) 4, MoleProp.LargeGap T.post L γ (η / 2) 0 (T.postLabels κ g) ∧ W g κ) :
    MoleProp.countEFree N L γ δ (0 : Mom d) Adm ≤
      (5 * T.windowK ^ 2 * (T.scaleFamily L P).card : ℕ∞) *
        MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) *
        ⨆ g ∈ Icc (0 : ℤ) 4, ⨆ P' ∈ T.scaleFamily L P,
          MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P' g) := by
  classical
  have hLp : 0 < L := by linarith
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτdef
  have hτ : 0 < τ := by positivity
  set K := T.windowK
  have hK : 1 ≤ K := by unfold K windowK; omega
  set F := MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d)
    (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) with hFdef
  set G := ⨆ g ∈ Icc (0 : ℤ) 4, ⨆ P' ∈ T.scaleFamily L P,
    MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P' g)
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ}
  have hAfin : A.Finite := (Mole.finite_restricted N hLp γ δ 0 β k0).subset fun _ h => h.2.1
  let Ag : ℤ → Set (D → (Fin d → ℤ)) := fun g =>
    {κ | κ ∈ A ∧ MoleProp.LargeGap T.post L γ (η / 2) 0 (T.postLabels κ g) ∧ W g κ}
  -- every decoration has a good multiplier
  have hcover : A ⊆ ⋃ g ∈ Icc (0 : ℤ) 4, Ag g := by
    intro κ hκ
    obtain ⟨g, hg, hLG, hWg⟩ := hW κ hκ.2.2 hκ.1.1
    exact Set.mem_biUnion hg ⟨hκ, hLG, hWg⟩
  -- the post problems
  let E : (ℕ × ℕ) × (Finset V → ℝ) → ℤ → Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) :=
    fun t g => {κ' | T.post.IsDecoration L 0 (T.postCharges c g) κ' ∧
      T.post.IsRestricted L γ δ 0 (T.postEnergy β c g τ t.1.1 t.1.2) (T.postCenters k0 c g) κ' ∧
      T.postAdm Adm W L γ (η / 2) t.2 g κ'}
  let idx : Finset ((ℕ × ℕ) × (Finset V → ℝ)) := (range K ×ˢ range K) ×ˢ T.scaleFamily L P
  have hk0' : ∀ g (z : Degen.RetainedDart N T.Y ⊕ Bool),
      T.postCenters k0 c g (T.post.mate z) = T.postCenters k0 c g z := by
    intro g z; rcases z with z | t
    · exact hk0 z.val
    · rfl
  have hE : ∀ g ∈ Icc (0 : ℤ) 4, ∀ t ∈ idx, (E t g).encard ≤ G := by
    intro g hg t ht
    refine (MoleProp.encard_le_countEFree T.post L γ δ 0 _ (T.postCharges c g)
      (T.postEnergy β c g τ t.1.1 t.1.2) (T.postCenters k0 c g) (hk0' g)).trans ?_
    refine le_iSup₂_of_le (f := fun g' (_ : g' ∈ Icc (0 : ℤ) 4) => ⨆ P' ∈ T.scaleFamily L P,
      MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdm Adm W L γ (η / 2) P' g')) g hg ?_
    exact le_iSup₂_of_le (f := fun P' _ => MoleProp.countEFree T.post L γ δ (0 : Mom d)
      (T.postAdm Adm W L γ (η / 2) P' g)) t.2 (mem_product.mp ht).2 le_rfl
  have hidx : (idx.card : ℕ∞) = K * K * (T.scaleFamily L P).card := by
    simp only [idx, card_product, card_range]; push_cast; ring
  -- the bound for one multiplier
  have hg_bound : ∀ g ∈ Icc (0 : ℤ) 4, (Ag g).encard ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G * F := by
    intro g hg
    have hAgfin : (Ag g).Finite := hAfin.subset fun _ h => h.1
    let B : Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) := ⋃ t ∈ idx, E t g
    have hmaps : ∀ κ ∈ Ag g, T.postLabels κ g ∈ B := by
      intro κ hκ
      obtain ⟨⟨hdec, hres, hadm⟩, hLG, hWg⟩ := hκ
      obtain ⟨jc, hjc, hwc⟩ := exists_window hτ hK (T.gamma_c_window hdec hres hg)
      obtain ⟨jd, hjd, hwd⟩ := exists_window hτ hK (T.gamma_d_window hdec hres hg)
      obtain ⟨P', hP', hcgr⟩ := T.exists_scaleFamily_cgr hloop hdeg hopen hL hdec.1 (hAdm κ hadm).2 g
      refine Set.mem_biUnion (x := ((jc, jd), P')) (mem_product.mpr ⟨mem_product.mpr ⟨hjc, hjd⟩, hP'⟩) ?_
      refine ⟨T.post_isDecoration hdec g, ⟨?_, ?_⟩, ⟨hLG, hcgr⟩, κ, hadm, hdec.1, hWg, rfl⟩
      · intro v hv
        rw [T.post_atoms] at hv
        obtain ⟨hvN, hvY⟩ := mem_sdiff.mp hv
        unfold postEnergy
        by_cases hc : v = T.c
        · subst hc; simpa only [ite_true] using hwc
        · by_cases hd : v = T.d
          · subst hd; simpa only [hc, ite_false, ite_true] using hwd
          · simp only [hc, hd, ite_false]
            rw [T.post_gamma L 0 hdec.1 g hvY]
            simp only [hc, hd, ite_false, add_zero]
            exact hres.1 v hvN
      · rintro (z | t)
        · exact hres.2 z.val
        · change ‖Molecule.kvec L 0 (T.postLabels κ g) (Sum.inr t) - (k0 T.y + (g : ℝ) • T.exitCharge c)‖ ≤ 1
          rw [T.kvec_postLabels_new, T.kvec_x_sub_y hdec]
          have : Molecule.kvec L 0 κ T.y + (g : ℝ) • T.exitCharge c - (k0 T.y + (g : ℝ) • T.exitCharge c) =
              Molecule.kvec L 0 κ T.y - k0 T.y := by abel
          rw [this]; exact hres.2 T.y
    have hfib : ∀ κ' ∈ B, {κ | κ ∈ Ag g ∧ T.postLabels κ g = κ'}.encard ≤ F := by
      intro κ' _
      by_cases hne : {κ | κ ∈ Ag g ∧ T.postLabels κ g = κ'}.Nonempty
      · obtain ⟨κ₀, ⟨hκ₀, hκ₀'⟩⟩ := hne
        refine (Set.encard_mono ?_).trans (MoleProp.fixed_deleted_fiber_encard_le N (N.atoms \ T.Y) L γ δ 0
          Adm c β k0 hk0 (MoleProp.deletedLabels N (N.atoms \ T.Y) κ₀))
        rintro κ ⟨⟨⟨hdec, hres, hadm⟩, _, _⟩, hκ'⟩
        refine ⟨hdec, hres, hadm, ?_⟩
        have hpost : T.postLabels κ g = T.postLabels κ₀ g := hκ'.trans hκ₀'.symm
        have hdec₀ := hκ₀.1.1
        -- the exits agree
        have hdiff : κ T.x - κ T.y = κ₀ T.x - κ₀ T.y := by
          apply latticePoint_injective hLp.ne'
          have h1 := T.kvec_x_sub_y hdec
          have h2 := T.kvec_x_sub_y hdec₀
          simp only [Molecule.kvec, zero_add] at h1 h2
          rw [latticePoint_sub', latticePoint_sub', h1, h2]
        have hnew := congrFun hpost (Sum.inr true)
        simp only [postLabels, Sum.elim_inr] at hnew
        rw [hdiff] at hnew
        have hy : κ T.y = κ₀ T.y := add_right_cancel hnew
        have hx : κ T.x = κ₀ T.x := by
          have := hdiff; rw [hy] at this; exact sub_left_injective this
        funext ⟨z, hz⟩
        simp only [MoleProp.deletedLabels]
        rcases T.dart_cases z with h | h | rfl | rfl | rfl | rfl
        · exfalso; apply hz
          exact ⟨fun h' => (mem_sdiff.mp h').2 h.1, fun h' => (mem_sdiff.mp h').2 h.2⟩
        · exact congrFun hpost (Sum.inl ⟨z, h.1, h.2⟩)
        · exact hx
        · exact hy
        · rw [hdec.1, hdec₀.1]; exact hx
        · rw [hdec.1, hdec₀.1]; exact hy
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.encard_empty]; exact bot_le
    have hB : B.encard ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G := by
      refine (encard_biUnion_le idx fun t => E t g).trans ?_
      calc ∑ t ∈ idx, (E t g).encard ≤ ∑ _t ∈ idx, G := sum_le_sum fun t ht => hE g hg t ht
        _ = (idx.card : ℕ∞) * G := by rw [sum_const, nsmul_eq_mul]
        _ = _ := by rw [hidx]
    calc (Ag g).encard ≤ B.encard * F := encard_le_mul_of_fiber hAgfin (fun κ => T.postLabels κ g) B hmaps F hfib
      _ ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G * F := mul_le_mul_left hB F
  calc A.encard ≤ (⋃ g ∈ Icc (0 : ℤ) 4, Ag g).encard := Set.encard_mono hcover
    _ ≤ ∑ g ∈ Icc (0 : ℤ) 4, (Ag g).encard := encard_biUnion_le _ _
    _ ≤ ∑ _g ∈ Icc (0 : ℤ) 4, (K * K * (T.scaleFamily L P).card : ℕ∞) * G * F := sum_le_sum hg_bound
    _ = 5 * ((K * K * (T.scaleFamily L P).card : ℕ∞) * G * F) := by
        rw [sum_const, nsmul_eq_mul]; rfl
    _ = (5 * K ^ 2 * (T.scaleFamily L P).card : ℕ∞) * F * G := by ring

end TwoExit
end WaveTurbulence.MoleProp4
