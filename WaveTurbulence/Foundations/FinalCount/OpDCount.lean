/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpCChain
public import WaveTurbulence.Foundations.FinalCount.G8R.ThmAOps
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitScaleFamily
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitWindows
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitLG
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitNorm
import Mathlib.Tactic

/-! # Operation (d): the counting inequality (DH23 L1865-L1867)

A modified clone of MOLEPROP4-T `TwoExit.countEFree_le` (the (Y2) count) for a chain `Y` of exempt (β) atoms of degree two:
LG is required only off `Bs ⊇ Y` (and at the two far ends `c, d ∉ Bs`), the piece factor is replaced by the uniqueness of the
chain labels given one exit label (`chain_agree`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **Choice of `g` keeping the large gap.** -/
theorem exists_post_largeGap_off {d : ℕ} {L γ η : ℝ} (hL : 1 ≤ L) (hL11 : 11 ≤ L ^ (η / 2))
    {w : Mom d} {κ : D → (Fin d → ℤ)} (hb : ∀ z, κ (N.mate z) = κ z)
    (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (Bs : Finset V) (hcB : T.c ∉ Bs) (hdB : T.d ∉ Bs)
    (hLG : ∀ x y : D, N.atom x = N.atom y → N.atom x ∉ Bs → N.out x ≠ N.out y →
      L ^ (-γ + η) ≤ ‖Molecule.kvec L w κ x - Molecule.kvec L w κ y‖) :
    ∃ g ∈ Icc (0 : ℤ) 4, ∀ z₁ z₂ : Degen.RetainedDart N T.Y ⊕ Bool, T.post.atom z₁ = T.post.atom z₂ →
      T.post.atom z₁ ∉ Bs \ T.Y → T.post.out z₁ ≠ T.post.out z₂ →
      L ^ (-γ + η / 2) ≤ ‖Molecule.kvec L w (T.postLabels κ g) z₁ - Molecule.kvec L w (T.postLabels κ g) z₂‖ := by
  have hLp : 0 < L := by linarith
  set lam := L ^ (-γ + η) with hlam
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hLp _
  have hkmx : Molecule.kvec L w κ (N.mate T.x) = Molecule.kvec L w κ T.x := by simp [Molecule.kvec, hb]
  have hkmy : Molecule.kvec L w κ (N.mate T.y) = Molecule.kvec L w κ T.y := by simp [Molecule.kvec, hb]
  obtain ⟨g, hg, hgood⟩ := exists_good_multiplier hlam0 (Molecule.kvec L w κ T.x) (Molecule.kvec L w κ T.y)
    (T.lgTargets L w κ) (T.card_lgTargets_le L w κ hcap) (by
      intro p hp
      unfold lgTargets at hp
      rcases mem_union.mp hp with hp | hp
      · obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
        obtain ⟨hzc, hzo⟩ := (mem_filter.mp hz).2
        simp only [ite_true]
        rw [← hkmx]
        refine hLG (N.mate T.x) z hzc.symm (by change T.c ∉ Bs; exact hcB) ?_
        rw [N.out_mate, T.out_x, hzo]; decide
      · obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
        obtain ⟨hzd, hzo⟩ := (mem_filter.mp hz).2
        simp only [Bool.false_eq_true, ite_false]
        rw [← hkmy]
        refine hLG (N.mate T.y) z hzd.symm (by change T.d ∉ Bs; exact hdB) ?_
        rw [N.out_mate, T.out_y, hzo]; decide)
  refine ⟨g, hg, ?_⟩
  -- the comparison `L^{-γ+η/2} ≤ λ/11 ≤ λ`
  have hcmp : L ^ (-γ + η / 2) ≤ lam / 11 := by
    have h2 : lam = L ^ (-γ + η / 2) * L ^ (η / 2) := by
      rw [hlam, ← Real.rpow_add hLp]; congr 1; ring
    rw [h2, le_div_iff₀ (by norm_num)]
    exact mul_le_mul_of_nonneg_left hL11 (Real.rpow_pos_of_pos hLp _).le
  have hcmp' : lam / 11 ≤ lam := by linarith
  intro z₁ z₂ hat hB hout
  have hk : ∀ z, Molecule.kvec L w (T.postLabels κ g) z = Sum.elim
      (fun z : Degen.RetainedDart N T.Y => Molecule.kvec L w κ z.val)
      (fun _ => Molecule.kvec L w κ T.y + (g : ℝ) • (Molecule.kvec L w κ T.x - Molecule.kvec L w κ T.y)) z := by
    rintro (z | t)
    · rfl
    · exact T.kvec_postLabels_new L w κ g t
  rw [hk, hk]
  rcases z₁ with z₁ | t₁ <;> rcases z₂ with z₂ | t₂
  · exact hcmp.trans (hcmp'.trans (hLG z₁.val z₂.val hat (fun hb => hB (mem_sdiff.mpr ⟨hb, (mem_sdiff.mp ((Degen.eraseAtoms N T.Y).atom_mem z₁)).2⟩)) hout))
  · -- new dart `t₂`, old dart `z₁` at the same atom
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [norm_sub_rev]
    cases t₂
    · -- at `c`, the new dart is incoming, `z₁` outgoing
      have hz : N.atom z₁.val = T.c := hat
      have hzo : N.out z₁.val = true := by
        have : T.post.out (Sum.inl z₁) ≠ false := hout
        simpa [post_out_inl] using this
      have := hgood (Molecule.kvec L w κ z₁.val, true) (by
        unfold lgTargets; exact mem_union_left _ (mem_image.mpr ⟨z₁.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
    · have hz : N.atom z₁.val = T.d := hat
      have hzo : N.out z₁.val = false := by
        have : T.post.out (Sum.inl z₁) ≠ true := hout
        simpa [post_out_inl] using this
      have := hgood (Molecule.kvec L w κ z₁.val, false) (by
        unfold lgTargets; exact mem_union_right _ (mem_image.mpr ⟨z₁.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
  · simp only [Sum.elim_inl, Sum.elim_inr]
    cases t₁
    · have hz : N.atom z₂.val = T.c := hat.symm
      have hzo : N.out z₂.val = true := by
        cases h : N.out z₂.val
        · exact absurd (show (false : Bool) = T.post.out (Sum.inl z₂) by rw [post_out_inl, h]) hout
        · rfl
      have := hgood (Molecule.kvec L w κ z₂.val, true) (by
        unfold lgTargets; exact mem_union_left _ (mem_image.mpr ⟨z₂.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
    · have hz : N.atom z₂.val = T.d := hat.symm
      have hzo : N.out z₂.val = false := by
        cases h : N.out z₂.val
        · rfl
        · exact absurd (show (true : Bool) = T.post.out (Sum.inl z₂) by rw [post_out_inl, h]) hout
      have := hgood (Molecule.kvec L w κ z₂.val, false) (by
        unfold lgTargets; exact mem_union_right _ (mem_image.mpr ⟨z₂.val, mem_filter.mpr ⟨mem_univ _, hz, hzo⟩, rfl⟩))
      exact hcmp.trans this
  · -- two new darts at the same atom: impossible (`c ≠ d`) or equal orientation
    exfalso
    cases t₁ <;> cases t₂
    · exact hout rfl
    · exact T.c_ne_d hat
    · exact T.c_ne_d hat.symm
    · exact hout rfl



/-- **The counting inequality of a two-exit (Y2) removal.** -/
theorem countEFree_le_chain (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (hch : ∀ b ∈ T.Y, N.outdeg b = 1 ∧ N.indeg b = 1) (hconnY : ∀ a ∈ T.Y, ∀ b ∈ T.Y, (piece N T.Y).SameComponent a b)
    (Bs : Finset V) (hcB : T.c ∉ Bs) (hdB : T.d ∉ Bs)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) {d : ℕ} {L γ δ η : ℝ}
    (hL : 1 ≤ L) (hL11 : 11 ≤ L ^ (η / 2)) (hδ : 0 < δ) (P : Finset V → ℝ)
    (Adm : (D → (Fin d → ℤ)) → Prop) (hAdm : ∀ κ, Adm κ → lgAdmOff N Bs L γ η P κ) :
    MoleProp.countEFree N L γ δ (0 : Mom d) Adm ≤
      (5 * T.windowK ^ 2 * (T.scaleFamily L P).card : ℕ∞) *
        ⨆ P' ∈ T.scaleFamily L P, MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P') := by
  classical
  have hLp : 0 < L := by linarith
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτdef
  have hτ : 0 < τ := by positivity
  set K := T.windowK
  have hK : 1 ≤ K := by unfold K windowK; omega
  set G := ⨆ P' ∈ T.scaleFamily L P, MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P')
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ}
  have hAfin : A.Finite := (Mole.finite_restricted N hLp γ δ 0 β k0).subset fun _ h => h.2.1
  let Ag : ℤ → Set (D → (Fin d → ℤ)) := fun g =>
    {κ | κ ∈ A ∧ ∀ z₁ z₂ : Degen.RetainedDart N T.Y ⊕ Bool, T.post.atom z₁ = T.post.atom z₂ →
      T.post.atom z₁ ∉ Bs \ T.Y → T.post.out z₁ ≠ T.post.out z₂ →
      L ^ (-γ + η / 2) ≤ ‖Molecule.kvec L 0 (T.postLabels κ g) z₁ - Molecule.kvec L 0 (T.postLabels κ g) z₂‖}
  -- every decoration has a good multiplier
  have hcover : A ⊆ ⋃ g ∈ Icc (0 : ℤ) 4, Ag g := by
    intro κ hκ
    obtain ⟨g, hg, hLG⟩ := T.exists_post_largeGap_off hL hL11 hκ.1.1 hcap Bs hcB hdB (hAdm κ hκ.2.2).1
    exact Set.mem_biUnion hg ⟨hκ, hLG⟩
  -- the post problems
  let E : (ℕ × ℕ) × (Finset V → ℝ) → ℤ → Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) :=
    fun t g => {κ' | T.post.IsDecoration L 0 (T.postCharges c g) κ' ∧
      T.post.IsRestricted L γ δ 0 (T.postEnergy β c g τ t.1.1 t.1.2) (T.postCenters k0 c g) κ' ∧
      lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) t.2 κ'}
  let idx : Finset ((ℕ × ℕ) × (Finset V → ℝ)) := (range K ×ˢ range K) ×ˢ T.scaleFamily L P
  have hk0' : ∀ g (z : Degen.RetainedDart N T.Y ⊕ Bool),
      T.postCenters k0 c g (T.post.mate z) = T.postCenters k0 c g z := by
    intro g z; rcases z with z | t
    · exact hk0 z.val
    · rfl
  have hE : ∀ g, ∀ t ∈ idx, (E t g).encard ≤ G := by
    intro g t ht
    refine (MoleProp.encard_le_countEFree T.post L γ δ 0 _ (T.postCharges c g)
      (T.postEnergy β c g τ t.1.1 t.1.2) (T.postCenters k0 c g) (hk0' g)).trans ?_
    exact le_iSup₂_of_le (f := fun P' _ => MoleProp.countEFree T.post L γ δ (0 : Mom d)
      (lgAdmOff T.post (Bs \ T.Y) L γ (η / 2) P')) t.2 (mem_product.mp ht).2 le_rfl
  have hidx : (idx.card : ℕ∞) = K * K * (T.scaleFamily L P).card := by
    simp only [idx, card_product, card_range]; push_cast; ring
  -- the bound for one multiplier
  have hg_bound : ∀ g ∈ Icc (0 : ℤ) 4, (Ag g).encard ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G := by
    intro g hg
    have hAgfin : (Ag g).Finite := hAfin.subset fun _ h => h.1
    let B : Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) := ⋃ t ∈ idx, E t g
    have hmaps : ∀ κ ∈ Ag g, T.postLabels κ g ∈ B := by
      intro κ hκ
      obtain ⟨⟨hdec, hres, hadm⟩, hLG⟩ := hκ
      obtain ⟨jc, hjc, hwc⟩ := exists_window hτ hK (T.gamma_c_window hdec hres hg)
      obtain ⟨jd, hjd, hwd⟩ := exists_window hτ hK (T.gamma_d_window hdec hres hg)
      obtain ⟨P', hP', hcgr⟩ := T.exists_scaleFamily_cgr hloop hdeg hopen hL hdec.1 (hAdm κ hadm).2 g
      refine Set.mem_biUnion (x := ((jc, jd), P')) (mem_product.mpr ⟨mem_product.mpr ⟨hjc, hjd⟩, hP'⟩) ?_
      refine ⟨T.post_isDecoration hdec g, ⟨?_, ?_⟩, hLG, hcgr⟩
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
    have hfib : ∀ κ' ∈ B, {κ | κ ∈ Ag g ∧ T.postLabels κ g = κ'}.encard ≤ 1 := by
      intro κ' _
      refine Set.encard_le_one_iff.mpr fun κ₁ κ₂ h₁ h₂ => ?_
      obtain ⟨⟨hA1, _⟩, hp1⟩ := h₁
      obtain ⟨⟨hA2, _⟩, hp2⟩ := h₂
      obtain ⟨hdec, hres, hadm⟩ := hA1
      obtain ⟨hdec₀, _, _⟩ := hA2
      have hpost : T.postLabels κ₁ g = T.postLabels κ₂ g := hp1.trans hp2.symm
      have hdiff : κ₁ T.x - κ₁ T.y = κ₂ T.x - κ₂ T.y := by
        apply latticePoint_injective hLp.ne'
        have h1 := T.kvec_x_sub_y hdec
        have h2 := T.kvec_x_sub_y hdec₀
        simp only [Molecule.kvec, zero_add] at h1 h2
        rw [latticePoint_sub', latticePoint_sub', h1, h2]
      have hnew := congrFun hpost (Sum.inr true)
      simp only [postLabels, Sum.elim_inr] at hnew
      rw [hdiff] at hnew
      have hy : κ₁ T.y = κ₂ T.y := add_right_cancel hnew
      have hx : κ₁ T.x = κ₂ T.x := by
        have := hdiff; rw [hy] at this; exact sub_left_injective this
      have hag := FinalCountG8.chain_agree N T.sub hch hconnY hLp.ne' hdec hdec₀ (z0 := T.x) T.atom_x hx
      funext z
      by_cases h1 : N.atom z ∈ T.Y
      · exact hag z h1
      · by_cases h2 : N.atom (N.mate z) ∈ T.Y
        · have := hag (N.mate z) h2
          rwa [hdec.1, hdec₀.1] at this
        · exact congrFun hpost (Sum.inl ⟨z, h1, h2⟩)
    have hB : B.encard ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G := by
      refine (encard_biUnion_le idx fun t => E t g).trans ?_
      calc ∑ t ∈ idx, (E t g).encard ≤ ∑ _t ∈ idx, G := sum_le_sum fun t ht => hE g t ht
        _ = (idx.card : ℕ∞) * G := by rw [sum_const, nsmul_eq_mul]
        _ = _ := by rw [hidx]
    calc (Ag g).encard ≤ B.encard * 1 := encard_le_mul_of_fiber hAgfin (fun κ => T.postLabels κ g) B hmaps 1 hfib
      _ ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G := by rw [mul_one]; exact hB
  calc A.encard ≤ (⋃ g ∈ Icc (0 : ℤ) 4, Ag g).encard := Set.encard_mono hcover
    _ ≤ ∑ g ∈ Icc (0 : ℤ) 4, (Ag g).encard := encard_biUnion_le _ _
    _ ≤ ∑ _g ∈ Icc (0 : ℤ) 4, (K * K * (T.scaleFamily L P).card : ℕ∞) * G := sum_le_sum hg_bound
    _ = 5 * ((K * K * (T.scaleFamily L P).card : ℕ∞) * G) := by
        rw [sum_const, nsmul_eq_mul]; rfl
    _ = (5 * K ^ 2 * (T.scaleFamily L P).card : ℕ∞) * G := by ring

end TwoExit
end WaveTurbulence.MoleProp4
