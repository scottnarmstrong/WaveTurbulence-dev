/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutPin

/-! # D2c-2 PROT-CUT: the terminal cut with designations inside the pieces, on `kernelProt`

For an admissible designation `F` (`CutPinFix`: `𝔫_b` at `s`, all designations at `s` strictly below `𝔫_a`),
**`CutTermData.kernelProt_cutPin`**:

`kernelProt LG F = c² (iζ_a)(iζ_b) Σ'_{e ∈ PairE} c_e ∫_{cutU} e^{πiA_e(u-s)}
    K_pre(T, u) K_in^{F}(u, s) Q_r^{F}(u, s) Q_g^{F}(u, s) du`

with the same pieces, outputs, multiplier factorization, constants and range `cutU` as (cut-term)
(`kernelProt_cutTerm`, the case `F = termFix`); the interior and side-couple pieces carry the pulled-back designations
`F ∘ βI`, `F ∘ βR`, `F ∘ βG`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}
variable (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
variable {s : ℝ} {F : GBranch LG.garden.tree → Option ℝ} (hF : CutPinFix Xp m inner s F)
include D hF

section SummandPin

variable {GZ : Garden 1} (hZ : (cpair m Qr Qg inner).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
include hZ hsZ
variable {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0)

/-- **The generalized terminal cut at one decoration** (summand level). -/
theorem summand_pin (L γ δ : ℝ) (H : LeafProfiles 1 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (Mp : (GNode LGp.garden.tree → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (hM : D.MultFactors M Mc Mp Mi Mr Mg) (T s' : ℝ) (k : Mom d) :
    protSummand L γ δ LG H M (fun _ => T) s' F k κ =
      (Mc (starA m L k (D.Φ hZ hsZ d κ).2.1) (starB m L k (D.Φ hZ hsZ d κ).2.1) *
          (cutEps m (D.Φ hZ hsZ d κ).2.1 : ℂ)) *
        ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s (D.Φ hZ hsZ d κ).2.1 u *
          (protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k (D.Φ hZ hsZ d κ).1 *
            (protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun x => F (D.βI x))
                (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.1) (D.Φ hZ hsZ d κ).2.2.1 *
              (protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βR y))
                  (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.1) (D.Φ hZ hsZ d κ).2.2.2.1 *
                protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βG y))
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
  have hphase := D.phase_cut hZ hsZ κ L γ δ k s
  unfold protSummand
  rw [hM, D.starA_eq hZ hsZ L k κ, D.starB_eq hZ hsZ L k κ, D.coset_P hZ hsZ L k κ, D.coset_I hZ hsZ L k κ,
    D.coset_R hZ hsZ L k κ, D.coset_G hZ hsZ L k κ, D.epsDec_cut hZ hsZ κ,
    D.protTime_cutPin hZ hsZ hF L γ δ T s' (cosetDecoration LG.garden L k κ.1), D.prodH_cut hZ hsZ κ L H k]
  simp only [hI, hR, hG, hP, hphase]
  rw [hsZ]
  rw [show ∀ (a b c J : ℂ), a * (b * J * c) = (a * b * c) * J from fun a b c J => by ring]
  conv_lhs => rw [← integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  congr 1
  funext u
  push_cast
  ring

end SummandPin

/-- **The generalized terminal cut on `kernelProt`**: (cut-term) with the admissible designations `F` carried by
the interior and side-couple pieces (o104 (P5), (P7)). -/
theorem kernelProt_cutPin (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mp : (GNode LGp.garden.tree → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mp Mi Mr Mg) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMp : ∀ K, ‖Mp K‖ ≤ CM)
    (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (T s' : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' F k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s e u *
            (kernelProt L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun x => F (D.βI x))
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                    (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βR y))
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βG y))
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  obtain ⟨GZ, hsZ, hZ⟩ := D.exists_GZ
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hMp 0)
  -- the bound of the full multiplier
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
  -- the protected-tree sum, reindexed
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hS : ∀ q, protSummand L γ δ LG H M (fun _ => T) s' F k (Φ.symm q) =
      (Mc (starA m L k q.2.1) (starB m L k q.2.1) * (cutEps m q.2.1 : ℂ)) *
        ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s q.2.1 u *
          (protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k q.1 *
            (protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun x => F (D.βI x))
                (k + latticePoint L q.2.1.1.1) q.2.2.1 *
              (protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βR y))
                  (k + latticePoint L q.2.1.1.2.1) q.2.2.2.1 *
                protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βG y))
                  (k + latticePoint L q.2.1.1.2.2) q.2.2.2.2))) := by
    intro q
    have := D.summand_pin hF hZ hsZ (Φ.symm q) L γ δ H M Mc Mp Mi Mr Mg hM T s' k
    rw [Φ.apply_symm_apply] at this
    exact this
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun _ => T) s' F k
    (card_lone_le_of_decodesTree D.dec) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun _ => T) s' F k (Φ.symm q) :=
    ((Φ.symm.summable_iff).mpr hsumG.of_norm)
  rw [tsum_cut_assembly (cutU LG Xp T s) (volume_cutU_ne_top LG Xp T s)
    (fun e => Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ))
    (fun e u => cutPh m (LG.garden.sig 0) L γ δ k s e u)
    (fun e u => (norm_cutPh m _ L γ δ k s e u).le) (fun e => stronglyMeasurable_cutPh m _ L γ δ k s e)
    (fun p u => protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k p)
    (fun e i u => protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun x => F (D.βI x))
      (k + latticePoint L e.1.1) i)
    (fun e r u => protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
      (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βR y)) (k + latticePoint L e.1.2.1) r)
    (fun e g u => protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
      (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βG y)) (k + latticePoint L e.1.2.2) g)
    (fun p => CM * leafMajorant L LGp (cutHp H) k p)
    (fun e i => CM * leafMajorant L LGi (cutHi Xp m H) (k + latticePoint L e.1.1) i)
    (fun e r => CM * leafMajorant L LGr (cutHr Xp m inner (LG.garden.sig 0) H) (k + latticePoint L e.1.2.1) r)
    (fun e g => CM * leafMajorant L LGg (cutHg Xp m inner (LG.garden.sig 0) H) (k + latticePoint L e.1.2.2) g)
    (fun p u => norm_protSummand_le L γ δ _ _ _ CM hMp _ _ _ _ p)
    (fun e i u => norm_protSummand_le L γ δ _ _ _ CM hMi _ _ _ _ i)
    (fun e r u => norm_protSummand_le L γ δ _ _ _ CM hMr _ _ _ _ r)
    (fun e g u => norm_protSummand_le L γ δ _ _ _ CM hMg _ _ _ _ g)
    ((summable_leafMajorant L LGp (cutHp H) k (fun _ => 0) 0 (card_lone_le_of_decodesTree D.decP)
      (D.hH_P hZ hsZ L H hH k)).mul_left CM)
    (fun e => (summable_leafMajorant L LGi (cutHi Xp m H) (k + latticePoint L e.1.1) (fun _ => 0) 0
      (card_lone_le_of_decodesTree D.decI) (D.hH_I hZ hsZ L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LGr _ (k + latticePoint L e.1.2.1) (fun _ => 0) 0
      (card_lone_le_of_plain D.decR.1.1) (D.hH_R hZ hsZ L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LGg _ (k + latticePoint L e.1.2.2) (fun _ => 0) 0
      (card_lone_le_of_plain D.decG.1.1) (D.hH_G hZ hsZ L H hH _)).mul_left CM)
    (fun p => stronglyMeasurable_protSummand L γ δ LGp _ Mp (fun _ _ => T) id _ k (fun _ => measurable_const)
      measurable_id p)
    (fun e i => stronglyMeasurable_protSummand L γ δ LGi _ Mi (fun u _ => u) (fun _ => s) _ _
      (fun _ => measurable_id) measurable_const i)
    (fun e r => stronglyMeasurable_protSummand L γ δ LGr _ Mr
      (fun u y => cupR m inner (LG.garden.sig 0) u s y.1.1) (fun _ => 0) _ _
      (fun y => measurable_cupR m inner _ s y.1.1) measurable_const r)
    (fun e g => stronglyMeasurable_protSummand L γ δ LGg _ Mg
      (fun u y => cupG m inner (LG.garden.sig 0) u s y.1.1) (fun _ => 0) _ _
      (fun y => measurable_cupG m inner _ s y.1.1) measurable_const g)
    _ hS hsum]
  -- the constants
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
      show pathSign (GZ.sig 0) (bPath m inner) = _
      rw [bPath, Comb.pathSign_append, pathSign_singleton, lonePath_sign, hsZ]
    rw [sa, sb]
  simp only [kernelProt_eq_tsum]
  set c := (coupling d L γ δ : ℂ)
  set Za := Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))
  set Zb := Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))
  set C₀ := c ^ LGp.garden.order * LGp.garden.zeta * (c ^ LGi.garden.order * LGi.garden.zeta *
    (c ^ LGr.garden.order * LGr.garden.zeta * (c ^ LGg.garden.order * LGg.garden.zeta)))
  have hpull : ∀ e : PairE m d,
      Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
        ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s e u *
              ((c ^ LGp.garden.order * LGp.garden.zeta * ∑' p : GenDecoration LGp.garden d (fun _ => 0) 0, protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k p) *
                ((c ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0, protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s
                  (fun x => F (D.βI x)) (k + latticePoint L e.1.1) i) *
                  ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0, protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βR y)) (k + latticePoint L e.1.2.1) r) *
                    (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0, protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βG y)) (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s e u *
              ((∑' p : GenDecoration LGp.garden d (fun _ => 0) 0, protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k p) *
                ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0, protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s
                  (fun x => F (D.βI x)) (k + latticePoint L e.1.1) i) *
                  ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0, protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βR y)) (k + latticePoint L e.1.2.1) r) *
                    (∑' g : GenDecoration LGg.garden d (fun _ => 0) 0, protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βG y)) (k + latticePoint L e.1.2.2) g))))) := by
    intro e
    have hu : ∀ u, cutPh m (LG.garden.sig 0) L γ δ k s e u *
              ((c ^ LGp.garden.order * LGp.garden.zeta * ∑' p : GenDecoration LGp.garden d (fun _ => 0) 0, protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k p) *
                ((c ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0, protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s
                  (fun x => F (D.βI x)) (k + latticePoint L e.1.1) i) *
                  ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0, protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βR y)) (k + latticePoint L e.1.2.1) r) *
                    (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0, protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βG y)) (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (cutPh m (LG.garden.sig 0) L γ δ k s e u *
              ((∑' p : GenDecoration LGp.garden d (fun _ => 0) 0, protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k p) *
                ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0, protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s
                  (fun x => F (D.βI x)) (k + latticePoint L e.1.1) i) *
                  ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0, protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βR y)) (k + latticePoint L e.1.2.1) r) *
                    (∑' g : GenDecoration LGg.garden d (fun _ => 0) 0, protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun y => F (D.βG y)) (k + latticePoint L e.1.2.2) g))))) := fun u => by ring
    simp_rw [hu, integral_const_mul]
    ring
  rw [tsum_congr hpull, tsum_mul_left, hord, hzeta, pow_add]
  ring

end CutTermData

end WaveTurbulence.Flower.ProtCut
