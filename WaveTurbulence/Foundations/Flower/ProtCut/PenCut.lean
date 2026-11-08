/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CheckNil

/-! # D2c PROT-CUT, MK-β: (P4) — penultimate and terminal nodes linked and both designated

For `X = appendChain Xp (pair m Qr Qg nil nil)` the penultimate chain node `𝔫_a` (at `Xp.lonePath`) is linked to the
terminal node `𝔫_b` (at `Xp.lonePath ++ [m.c]`). With both designated at `s` (`ProtCfg.penTerm`, `cfg_penTerm_fix`),
**`CutTermData.kernelProt_pen`**:
`kernelProt = c² (iζ_a)(iζ_b) Σ'_e c_e K_pre(T, s) K_in(s, s) Q_r(s, s) Q_g(s, s)` (the linked phases cancel:
`cutPh … s e s = 1`; `K_in` is the trivial interior of code `nil`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- `𝔫_a` and `𝔫_b` designated at `s`. -/
def penFix (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (s : ℝ) {T : Fin 1 → TTree} (b : GBranch T) :
    Option ℝ :=
  if b.1.2 = Xp.lonePath ∨ b.1.2 = Xp.lonePath ++ bPath m inner then some s else none

theorem cutPh_self (m : MiniTreeCode) (ζ : ℤˣ) (L γ δ : ℝ) {d : ℕ} (k : Mom d) (s : ℝ) (e : PairE m d) :
    cutPh m ζ L γ δ k s e s = 1 := by
  unfold cutPh
  simp

theorem cfg_penTerm_fix (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (s t up : ℝ) {T : Fin 1 → TTree} :
    (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t up : GBranch T → Option ℝ) =
      penFix Xp m .nil s := by
  have h1 : (appendChain Xp (cpair m Qr Qg .nil)).lonePath.dropLast = Xp.lonePath ++ bPath m .nil :=
    lonePath_dropLast_cutTerm Xp m Qr Qg .nil
  have h2 : (appendChain Xp (cpair m Qr Qg .nil)).lonePath.dropLast.dropLast = Xp.lonePath := by
    rw [h1]; simp [bPath, RegChain.lonePath]
  funext b
  unfold ProtCfg.fix ProtCfg.pins penFix
  rw [if_pos (Fin.val_eq_zero _), h2, h1]
  simp only [List.lookup]
  by_cases ha : b.1.2 = Xp.lonePath
  · rw [show (b.1.2 == Xp.lonePath) = true from beq_iff_eq.mpr ha, if_pos (Or.inl ha)]
  · rw [show (b.1.2 == Xp.lonePath) = false from beq_eq_false_iff_ne.mpr ha]
    by_cases hb : b.1.2 = Xp.lonePath ++ bPath m .nil
    · rw [show (b.1.2 == Xp.lonePath ++ bPath m .nil) = true from beq_iff_eq.mpr hb, if_pos (Or.inr hb)]
    · rw [show (b.1.2 == Xp.lonePath ++ bPath m .nil) = false from beq_eq_false_iff_ne.mpr hb,
        if_neg (fun h => h.elim ha hb)]

/-- Products of four sums, one of them independent of the exceptional data (no integral). -/
theorem tsum_pen_assembly {Dp E Di Dr Dg : Type*} (c : E → ℂ) (Sp : Dp → ℂ) (Si : E → Di → ℂ) (Sr : E → Dr → ℂ)
    (Sg : E → Dg → ℂ) (nSp : Summable fun p => ‖Sp p‖) (nSi : ∀ e, Summable fun i => ‖Si e i‖)
    (nSr : ∀ e, Summable fun r => ‖Sr e r‖) (nSg : ∀ e, Summable fun g => ‖Sg e g‖)
    (S : Dp × (E × (Di × (Dr × Dg))) → ℂ)
    (hS : ∀ q, S q = c q.2.1 * (Sp q.1 * (Si q.2.1 q.2.2.1 * (Sr q.2.1 q.2.2.2.1 * Sg q.2.1 q.2.2.2.2))))
    (hsum : Summable S) :
    ∑' q, S q = ∑' e, c e * ((∑' p, Sp p) * ((∑' i, Si e i) * ((∑' r, Sr e r) * ∑' g, Sg e g))) := by
  let σ : E × (Dp × (Di × (Dr × Dg))) ≃ Dp × (E × (Di × (Dr × Dg))) :=
    { toFun := fun x => (x.2.1, (x.1, x.2.2))
      invFun := fun q => (q.2.1, (q.1, q.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← σ.tsum_eq]
  have hslice : ∀ e, Summable fun r : Dp × (Di × (Dr × Dg)) => S (σ (e, r)) := by
    intro e
    have n4 := nSp.mul_norm ((nSi e).mul_norm ((nSr e).mul_norm (nSg e)))
    simp only [hS]
    exact (n4.of_norm.mul_left (c e))
  have hs' : Summable fun x => S (σ x) := (σ.summable_iff).mpr hsum
  rw [Summable.tsum_prod' hs' hslice]
  refine tsum_congr fun e => ?_
  simp only [hS]
  show ∑' r : Dp × (Di × (Dr × Dg)), c e * (Sp r.1 * (Si e r.2.1 * (Sr e r.2.2.1 * Sg e r.2.2.2))) = _
  rw [tsum_mul_left]
  congr 1
  rw [tsum_mul_tsum_of_summable_norm (nSr e) (nSg e),
    tsum_mul_tsum_of_summable_norm (nSi e) ((nSr e).mul_norm (nSg e)),
    tsum_mul_tsum_of_summable_norm nSp ((nSi e).mul_norm ((nSr e).mul_norm (nSg e)))]

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} (D : CutTermData LG Xp m Qr Qg .nil LGp LGi LGr LGg)
include D

section Pen

variable {GZ : Garden 1} (hZ : (cpair m Qr Qg .nil).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
include hZ hsZ

theorem penFix_eq (s : ℝ) :
    (penFix Xp m .nil s : GBranch LG.garden.tree → Option ℝ) =
      Function.update (termFix Xp m .nil s) (D.aB hZ hsZ) (some s) := by
  funext b
  by_cases hb : b = D.aB hZ hsZ
  · subst hb
    rw [Function.update_self]
    unfold penFix
    exact if_pos (Or.inl (by rw [D.aB_path hZ hsZ]))
  · rw [Function.update_of_ne hb]
    unfold penFix termFix
    have ha : b.1.2 ≠ Xp.lonePath := fun h => hb (Subtype.ext ((Prod.ext (Subsingleton.elim _ _) h).trans
      (D.aB_path hZ hsZ).symm))
    by_cases h2 : b.1.2 = Xp.lonePath ++ bPath m .nil
    · rw [if_pos (Or.inr h2), if_pos h2]
    · rw [if_neg (fun h => h.elim ha h2), if_neg h2]

/-- **(P4) at one decoration.** -/
theorem summand_pen {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L γ δ : ℝ) (H : LeafProfiles 1 d)
    (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (Mp : (GNode LGp.garden.tree → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (hM : D.MultFactors M Mc Mp Mi Mr Mg) (T s s' : ℝ) (hsT : s ≤ T)
    (k : Mom d) :
    protSummand L γ δ LG H M (fun _ => T) s' (penFix Xp m .nil s) k κ =
      (Mc (starA m L k (D.Φ hZ hsZ d κ).2.1) (starB m L k (D.Φ hZ hsZ d κ).2.1) *
          (cutEps m (D.Φ hZ hsZ d κ).2.1 : ℂ)) *
        (protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) s (fun _ => none) k (D.Φ hZ hsZ d κ).1 *
          (protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => s) s (fun _ => none)
              (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.1) (D.Φ hZ hsZ d κ).2.2.1 *
            (protSummand L γ δ LGr (cutHr Xp m .nil (LG.garden.sig 0) H) Mr
                (fun y => cupR m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.1) (D.Φ hZ hsZ d κ).2.2.2.1 *
              protSummand L γ δ LGg (cutHg Xp m .nil (LG.garden.sig 0) H) Mg
                (fun y => cupG m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.2) (D.Φ hZ hsZ d κ).2.2.2.2))) := by
  have hI : cosetDecoration LG.garden L k κ.1 ∘ ((D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιi) =
      cosetDecoration LGi.garden L (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.1) ((D.Φ hZ hsZ d κ).2.2.1).1 := by
    rw [← D.coset_I hZ hsZ L k κ]
    funext z
    simp [D.ιI_eq hZ hsZ]
  have hR : cosetDecoration LG.garden L k κ.1 ∘ ((D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιr) =
      cosetDecoration LGr.garden L (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.1)
        ((D.Φ hZ hsZ d κ).2.2.2.1).1 := by
    rw [← D.coset_R hZ hsZ L k κ]
    funext z
    simp [D.ιR_eq hZ hsZ]
  have hG : cosetDecoration LG.garden L k κ.1 ∘ ((D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιg) =
      cosetDecoration LGg.garden L (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.2)
        ((D.Φ hZ hsZ d κ).2.2.2.2).1 := by
    rw [← D.coset_G hZ hsZ L k κ]
    funext z
    simp [D.ιG_eq hZ hsZ]
  have hP : cosetDecoration LG.garden L k κ.1 ∘ (D.gd hZ hsZ).ι₁ =
      cosetDecoration LGp.garden L k ((D.Φ hZ hsZ d κ).1).1 := rfl
  have hphase := D.phase_cut hZ hsZ κ L γ δ k s s
  unfold protSummand
  rw [hM, D.starA_eq hZ hsZ L k κ, D.starB_eq hZ hsZ L k κ, D.coset_P hZ hsZ L k κ, D.coset_I hZ hsZ L k κ,
    D.coset_R hZ hsZ L k κ, D.coset_G hZ hsZ L k κ, D.epsDec_cut hZ hsZ κ, D.penFix_eq hZ hsZ s,
    D.protTime_glueT hZ hsZ L γ δ T s s' s, D.protTime_pairT hZ hsZ L γ δ T s s' s le_rfl hsT,
    D.prodH_cut hZ hsZ κ L H k]
  simp only [Function.comp_assoc, hI, hR, hG, hP]
  rw [hphase, cutPh_self]
  rw [hsZ]
  push_cast
  ring

end Pen

/-- **(P4) on `kernelProt`**: the linked penultimate and terminal nodes designated at `s`. -/
theorem kernelProt_pen (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mp : (GNode LGp.garden.tree → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mp Mi Mr Mg) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMp : ∀ K, ‖Mp K‖ ≤ CM)
    (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (T s s' : ℝ) (hsT : s ≤ T)
    (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (penFix Xp m .nil s) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          (kernelProt L γ δ LGp (cutHp H) Mp (fun _ => T) s (fun _ => none) k (fun _ => 0) 0 *
            (kernelProt L γ δ LGi (cutHi Xp m H) Mi (fun _ => s) s (fun _ => none)
                (k + latticePoint L e.1.1) (fun _ => 0) 0 *
              (kernelProt L γ δ LGr (cutHr Xp m .nil (LG.garden.sig 0) H) Mr
                  (fun y => cupR m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                kernelProt L γ δ LGg (cutHg Xp m .nil (LG.garden.sig 0) H) Mg
                  (fun y => cupG m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  obtain ⟨GZ, hsZ, hZ⟩ := D.exists_GZ
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hMp 0)
  have hMb : ∀ K, ‖M K‖ ≤ CM * (CM * (CM * (CM * CM))) := by
    intro K
    rw [hM K, norm_mul, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact hMc _ _
    · exact hMp _
    · exact hMi _
    · exact hMr _
    · exact hMg _
  set Φ := D.Φ hZ hsZ d
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hS : ∀ q, protSummand L γ δ LG H M (fun _ => T) s' (penFix Xp m .nil s) k (Φ.symm q) =
      (Mc (starA m L k q.2.1) (starB m L k q.2.1) * (cutEps m q.2.1 : ℂ)) *
        (protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) s (fun _ => none) k q.1 *
          (protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => s) s (fun _ => none)
              (k + latticePoint L q.2.1.1.1) q.2.2.1 *
            (protSummand L γ δ LGr (cutHr Xp m .nil (LG.garden.sig 0) H) Mr
                (fun y => cupR m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                (k + latticePoint L q.2.1.1.2.1) q.2.2.2.1 *
              protSummand L γ δ LGg (cutHg Xp m .nil (LG.garden.sig 0) H) Mg
                (fun y => cupG m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                (k + latticePoint L q.2.1.1.2.2) q.2.2.2.2))) := by
    intro q
    have := D.summand_pen hZ hsZ (Φ.symm q) L γ δ H M Mc Mp Mi Mr Mg hM T s s' hsT k
    rw [Φ.apply_symm_apply] at this
    exact this
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun _ => T) s' (penFix Xp m .nil s) k
    (card_lone_le_of_decodesTree D.dec) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun _ => T) s' (penFix Xp m .nil s) k (Φ.symm q) :=
    (Φ.symm.summable_iff).mpr hsumG.of_norm
  rw [tsum_pen_assembly (fun e => Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ))
    (fun p => protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) s (fun _ => none) k p)
    (fun e i => protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => s) s (fun _ => none)
      (k + latticePoint L e.1.1) i)
    (fun e r => protSummand L γ δ LGr (cutHr Xp m .nil (LG.garden.sig 0) H) Mr
      (fun y => cupR m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r)
    (fun e g => protSummand L γ δ LGg (cutHg Xp m .nil (LG.garden.sig 0) H) Mg
      (fun y => cupG m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g)
    (summable_protSummand_norm L γ δ LGp _ Mp CM hMp _ _ _ _ (card_lone_le_of_decodesTree D.decP)
      (fun ℓ hℓ => D.hH_P hZ hsZ L H hH _ ℓ hℓ))
    (fun e => summable_protSummand_norm L γ δ LGi _ Mi CM hMi _ _ _ _ (card_lone_le_of_decodesTree D.decI)
      (fun ℓ hℓ => D.hH_I hZ hsZ L H hH _ ℓ hℓ))
    (fun e => summable_protSummand_norm L γ δ LGr _ Mr CM hMr _ _ _ _ (card_lone_le_of_plain D.decR.1.1)
      (fun ℓ hℓ => D.hH_R hZ hsZ L H hH _ ℓ hℓ))
    (fun e => summable_protSummand_norm L γ δ LGg _ Mg CM hMg _ _ _ _ (card_lone_le_of_plain D.decG.1.1)
      (fun ℓ hℓ => D.hH_G hZ hsZ L H hH _ ℓ hℓ)) _ hS hsum]
  have hord : LG.garden.order = LGp.garden.order + (LGi.garden.order + LGr.garden.order + LGg.garden.order + 2) := by
    rw [(D.gd hZ hsZ).order_glue, (D.hp hZ hsZ).order_pair]
  have hzeta : LG.garden.zeta = LGp.garden.zeta * ((Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
      (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        (LGi.garden.zeta * (LGr.garden.zeta * LGg.garden.zeta))) := by
    rw [(D.gd hZ hsZ).zeta_glue, (D.hp hZ hsZ).zeta_pair]
    have sa : GZ.sign (D.hp hZ hsZ).rootB.toNode = LG.garden.sig 0 := by
      show pathSign (GZ.sig 0) [] = _
      simp [pathSign, hsZ]
    have sb : GZ.sign (D.hp hZ hsZ).bB.toNode = slotSign (LG.garden.sig 0) m.c := by
      show pathSign (GZ.sig 0) (bPath m .nil) = _
      rw [bPath, Comb.pathSign_append, pathSign_singleton, lonePath_sign, hsZ]
    rw [sa, sb]
  simp only [kernelProt_eq_tsum]
  set c := (coupling d L γ δ : ℂ)
  set C₀ := c ^ LGp.garden.order * LGp.garden.zeta * (c ^ LGi.garden.order * LGi.garden.zeta *
    (c ^ LGr.garden.order * LGr.garden.zeta * (c ^ LGg.garden.order * LGg.garden.zeta)))
  have hpull : ∀ e : PairE m d,
      Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
        ((c ^ LGp.garden.order * LGp.garden.zeta * ∑' p : GenDecoration LGp.garden d (fun _ => 0) 0,
            protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) s (fun _ => none) k p) *
          ((c ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
              protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => s) s (fun _ => none) (k + latticePoint L e.1.1) i) *
            ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
              protSummand L γ δ LGr (cutHr Xp m .nil (LG.garden.sig 0) H) Mr
                (fun y => cupR m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                (k + latticePoint L e.1.2.1) r) *
              (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                protSummand L γ δ LGg (cutHg Xp m .nil (LG.garden.sig 0) H) Mg
                  (fun y => cupG m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ((∑' p : GenDecoration LGp.garden d (fun _ => 0) 0,
              protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) s (fun _ => none) k p) *
            ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
                protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => s) s (fun _ => none)
                  (k + latticePoint L e.1.1) i) *
              ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
                protSummand L γ δ LGr (cutHr Xp m .nil (LG.garden.sig 0) H) Mr
                  (fun y => cupR m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) r) *
                ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGg (cutHg Xp m .nil (LG.garden.sig 0) H) Mg
                    (fun y => cupG m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) g)))) := fun e => by ring
  rw [tsum_congr hpull, tsum_mul_left, hord, hzeta, pow_add]
  ring

end CutTermData

/-- (P4) in D3's configuration form `ProtCfg.penTerm` (`X = appendChain Xp (pair m Qr Qg nil nil)`). -/
theorem kernelProt_penTerm_cfg {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain}
    {m : MiniTreeCode} {Qr Qg : RegCpl} (D : CutTermData LG Xp m Qr Qg .nil LGp LGi LGr LGg) (L γ δ : ℝ) {d : ℕ}
    (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mp : (GNode LGp.garden.tree → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mp Mi Mr Mg) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMp : ∀ K, ‖Mp K‖ ≤ CM)
    (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (T s s' t : ℝ) (hsT : s ≤ T)
    (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg .nil)) s t T) k
        (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          (kernelProt L γ δ LGp (cutHp H) Mp (fun _ => T) s (fun _ => none) k (fun _ => 0) 0 *
            (kernelProt L γ δ LGi (cutHi Xp m H) Mi (fun _ => s) s (fun _ => none)
                (k + latticePoint L e.1.1) (fun _ => 0) 0 *
              (kernelProt L γ δ LGr (cutHr Xp m .nil (LG.garden.sig 0) H) Mr
                  (fun y => cupR m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                kernelProt L γ δ LGg (cutHg Xp m .nil (LG.garden.sig 0) H) Mg
                  (fun y => cupG m .nil (LG.garden.sig 0) s s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [cfg_penTerm_fix]
  exact D.kernelProt_pen L γ δ H hH M Mc Mp Mi Mr Mg hM CM hMc hMp hMi hMr hMg T s s' hsT k

#print axioms CutTermData.kernelProt_pen
#print axioms kernelProt_penTerm_cfg

end WaveTurbulence.Flower.ProtCut
