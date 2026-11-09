/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpDW
import Mathlib.Tactic

/-! # The multiplier of operation (d)/(e) when a far end is protected (packet L6-COUNT, Case6TopLow)

Main's `TwoExit.exists_post_largeGap_off` (OpDCount) chooses `g ∈ {0,…,4}` keeping LG off `Bs ∖ Y` in the post,
assuming both far ends `c, d ∉ Bs`. In case (6d) a far end of the removed theta chain may be a protected degree-two atom
(a remaining chain atom, `∈ Bs`), where the post requires nothing. `exists_postGoodOff_any` drops the hypotheses
`c, d ∉ Bs`: the targets of the multiplier choice are restricted to the far ends outside `Bs`.

Adapted from main `FinalCount/OpDCount.lean` (`exists_post_largeGap_off`; sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.Count
open WaveTurbulence.MoleProp4

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Choice of `g` keeping the large gap off `Bs`**, far ends arbitrary. -/
theorem exists_postGoodOff_any {N : Molecule V D} (T : TwoExit N) {d : ℕ} {L γ η : ℝ} (hL : 1 ≤ L)
    (hL11 : 11 ≤ L ^ (η / 2)) {κ : D → (Fin d → ℤ)} (hb : ∀ z, κ (N.mate z) = κ z)
    (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) (Bs : Finset V)
    (hLG : ∀ x y : D, N.atom x = N.atom y → N.atom x ∉ Bs → N.out x ≠ N.out y →
      L ^ (-γ + η) ≤ ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖) :
    ∃ g ∈ Icc (0 : ℤ) 4, T.PostGoodOff Bs L γ (η / 2) κ g := by
  classical
  have hLp : 0 < L := by linarith
  set lam := L ^ (-γ + η) with hlam
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hLp _
  set w : Mom d := 0
  have hkmx : Molecule.kvec L w κ (N.mate T.x) = Molecule.kvec L w κ T.x := by simp [Molecule.kvec, hb]
  have hkmy : Molecule.kvec L w κ (N.mate T.y) = Molecule.kvec L w κ T.y := by simp [Molecule.kvec, hb]
  set Z := (T.lgTargets L w κ).filter fun pr => if pr.2 = true then T.c ∉ Bs else T.d ∉ Bs with hZ
  obtain ⟨g, hg, hgood⟩ := exists_good_multiplier hlam0 (Molecule.kvec L w κ T.x) (Molecule.kvec L w κ T.y)
    Z ((card_filter_le _ _).trans (T.card_lgTargets_le L w κ hcap)) (by
      intro pr hpr
      obtain ⟨hp, hpB⟩ := mem_filter.mp hpr
      unfold TwoExit.lgTargets at hp
      rcases mem_union.mp hp with hp | hp
      · obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
        obtain ⟨hzc, hzo⟩ := (mem_filter.mp hz).2
        simp only [ite_true] at hpB ⊢
        rw [← hkmx]
        refine hLG (N.mate T.x) z hzc.symm (by change T.c ∉ Bs; exact hpB) ?_
        rw [N.out_mate, T.out_x, hzo]; decide
      · obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
        obtain ⟨hzd, hzo⟩ := (mem_filter.mp hz).2
        simp only [Bool.false_eq_true, ite_false] at hpB ⊢
        rw [← hkmy]
        refine hLG (N.mate T.y) z hzd.symm (by change T.d ∉ Bs; exact hpB) ?_
        rw [N.out_mate, T.out_y, hzo]; decide)
  refine ⟨g, hg, ?_⟩
  have hcmp : L ^ (-γ + η / 2) ≤ lam / 11 := by
    have h2 : lam = L ^ (-γ + η / 2) * L ^ (η / 2) := by
      rw [hlam, ← Real.rpow_add hLp]; congr 1; ring
    rw [h2, le_div_iff₀ (by norm_num)]
    exact mul_le_mul_of_nonneg_left hL11 (Real.rpow_pos_of_pos hLp _).le
  have hcmp' : lam / 11 ≤ lam := by linarith
  have hcB : ∀ z₁ : Degen.RetainedDart N T.Y ⊕ Bool, T.post.atom z₁ = T.c → T.post.atom z₁ ∉ Bs \ T.Y →
      T.c ∉ Bs := fun z₁ hz hB hc => hB (by rw [hz]; exact mem_sdiff.mpr ⟨hc, T.c_notMem⟩)
  have hdB : ∀ z₁ : Degen.RetainedDart N T.Y ⊕ Bool, T.post.atom z₁ = T.d → T.post.atom z₁ ∉ Bs \ T.Y →
      T.d ∉ Bs := fun z₁ hz hB hc => hB (by rw [hz]; exact mem_sdiff.mpr ⟨hc, T.d_notMem⟩)
  intro z₁ z₂ hat hB hout
  have hk : ∀ z, Molecule.kvec L w (T.postLabels κ g) z = Sum.elim
      (fun z : Degen.RetainedDart N T.Y => Molecule.kvec L w κ z.val)
      (fun _ => Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y)) z := by
    rintro (z | t)
    · rfl
    · exact T.kvec_postLabels_new L w κ g t
  rw [hk, hk]
  rcases z₁ with z₁ | t₁ <;> rcases z₂ with z₂ | t₂
  · exact hcmp.trans (hcmp'.trans (hLG z₁.val z₂.val hat (fun hb => hB (mem_sdiff.mpr
      ⟨hb, (mem_sdiff.mp ((Degen.eraseAtoms N T.Y).atom_mem z₁)).2⟩)) hout))
  · simp only [Sum.elim_inl, Sum.elim_inr]
    rw [norm_sub_rev]
    cases t₂
    · have hz : N.atom z₁.val = T.c := hat
      have hzo : N.out z₁.val = true := by
        have : T.post.out (Sum.inl z₁) ≠ false := hout
        simpa [TwoExit.post_out_inl] using this
      have hc := hcB (Sum.inl z₁) hz hB
      have := hgood (Molecule.kvec L w κ z₁.val, true) (by
        refine mem_filter.mpr ⟨?_, by simpa using hc⟩
        unfold TwoExit.lgTargets
        exact mem_union_left _ (mem_image.mpr ⟨z₁.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
    · have hz : N.atom z₁.val = T.d := hat
      have hzo : N.out z₁.val = false := by
        have : T.post.out (Sum.inl z₁) ≠ true := hout
        simpa [TwoExit.post_out_inl] using this
      have hd := hdB (Sum.inl z₁) hz hB
      have := hgood (Molecule.kvec L w κ z₁.val, false) (by
        refine mem_filter.mpr ⟨?_, by simpa using hd⟩
        unfold TwoExit.lgTargets
        exact mem_union_right _ (mem_image.mpr ⟨z₁.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
  · simp only [Sum.elim_inl, Sum.elim_inr]
    cases t₁
    · have hz : N.atom z₂.val = T.c := hat.symm
      have hzo : N.out z₂.val = true := by
        cases h : N.out z₂.val
        · exact absurd (show (false : Bool) = T.post.out (Sum.inl z₂) by rw [TwoExit.post_out_inl, h]) hout
        · rfl
      have hc := hcB (Sum.inr false) rfl hB
      have := hgood (Molecule.kvec L w κ z₂.val, true) (by
        refine mem_filter.mpr ⟨?_, by simpa using hc⟩
        unfold TwoExit.lgTargets
        exact mem_union_left _ (mem_image.mpr ⟨z₂.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
    · have hz : N.atom z₂.val = T.d := hat.symm
      have hzo : N.out z₂.val = false := by
        cases h : N.out z₂.val
        · rfl
        · exact absurd (show (true : Bool) = T.post.out (Sum.inl z₂) by rw [TwoExit.post_out_inl, h]) hout
      have hd := hdB (Sum.inr true) rfl hB
      have := hgood (Molecule.kvec L w κ z₂.val, false) (by
        refine mem_filter.mpr ⟨?_, by simpa using hd⟩
        unfold TwoExit.lgTargets
        exact mem_union_right _ (mem_image.mpr ⟨z₂.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
  · exfalso
    cases t₁ <;> cases t₂
    · exact hout rfl
    · exact T.c_ne_d hat
    · exact T.c_ne_d hat.symm
    · exact hout rfl

end WaveTurbulence.GammaLow.FinalCount.Count
