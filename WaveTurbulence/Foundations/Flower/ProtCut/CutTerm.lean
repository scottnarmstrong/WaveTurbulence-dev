/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutTermSummand

/-! # D2c PROT-CUT, milestone MK-α: the (cut-term) identity (o73 Prop 13.1) on `kernelProt`

For a protected paired tree `LG` with code `X = appendChain Xp (pair m Qr Qg inner nil)` (the terminal node `𝔫_b`
of the chain and its partner `𝔫_a`), with `𝔫_b` designated at `s` (`termFix`), output `k` and upper clock `T`:

`kernelProt LG (term at s) = c² (iζ_a)(iζ_b) Σ'_{e ∈ PairE} c_e ∫_{cutU} e^{πiA_e(u-s)}
    K_pre(T, u) K_in(u, s) Q_r(u, s) Q_g(u, s) du`   (**`kernelProt_cutTerm`**)

* the four pieces are unpinned `kernelProt`s of the prefix `LGp` (code `Xp`, lone-port time `u`), the interior `LGi`
  (code `inner`, upper clock `u`, lone-port time `s`) and the side couples `LGr`, `LGg` (codes `Qr`, `Qg`, upper
  clocks `u` at `𝔫_a` and `s` at `𝔫_b`, `cupR`/`cupG`);
* their outputs `k`, `k + e.x/L`, `k + e.yr/L`, `k + e.yg/L` are affine in `(k, e)`;
* the multiplier factors (`MultFactors`), `c_e = M_cut(star_a, star_b) · ε_a ε_b`, `A_e = ζ δ L^{2γ} Ω_{𝔫_a}`;
* `cutU = {max(s, 𝔏_a, 0) < u < min(T, 𝔏_a + 1)}`.

Sizes and incoherency indices of the pieces: `CutBook.lean`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-! ### Majorants and measurability of summands -/

theorem norm_protSummand_le (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (C : ℝ) (hm : ∀ K, ‖m K‖ ≤ C)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) :
    ‖protSummand L γ δ LG H m up s fix k₀ κ‖ ≤ C * leafMajorant L LG H k₀ κ := by
  unfold protSummand leafMajorant
  rw [norm_mul, norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have he := abs_epsDec_le_one LG.garden κ.1
  have hp := norm_protTime_le_one L γ δ LG up s fix (cosetDecoration LG.garden L k₀ κ.1)
  have hprod : 0 ≤ ∏ ℓ ∈ inputLeaves LG.garden, |H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)| :=
    prod_nonneg fun _ _ => abs_nonneg _
  have hC : 0 ≤ C := (norm_nonneg _).trans (hm 0)
  calc ‖m (cosetDecoration LG.garden L k₀ κ.1)‖ * (|epsDec LG.garden κ.1| *
        ‖protTime L γ δ LG up s fix (cosetDecoration LG.garden L k₀ κ.1)‖ *
        ∏ ℓ ∈ inputLeaves LG.garden, |H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)|)
      ≤ C * (1 * 1 * ∏ ℓ ∈ inputLeaves LG.garden, |H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)|) := by
        gcongr
        · exact hm _
    _ = _ := by ring

theorem summable_protSummand_norm (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (C : ℝ) (hm : ∀ K, ‖m K‖ ≤ C)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d (fun _ => 0) 0 => ‖protSummand L γ δ LG H m up s fix k₀ κ‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_protSummand_le L γ δ LG H m C hm up s fix k₀)
    ((summable_leafMajorant L LG H k₀ (fun _ => 0) 0 hlone hH).mul_left C)

theorem stronglyMeasurable_protSummand (L γ δ : ℝ) {w d : ℕ} (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : ℝ → GBranch LG.garden.tree → ℝ) (sl : ℝ → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d) (hup : ∀ b, Measurable fun u => up u b)
    (hsl : Measurable sl) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    StronglyMeasurable fun u => protSummand L γ δ LG H m (up u) (sl u) fix k₀ κ := by
  unfold protSummand
  exact stronglyMeasurable_const.mul ((stronglyMeasurable_const.mul
    (stronglyMeasurable_protTime_param L γ δ LG up sl fix _ hup hsl)).mul stronglyMeasurable_const)

theorem measurable_cupR (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (s : ℝ) (j : Fin 2) :
    Measurable fun u => cupR m inner ζ u s j := by
  unfold cupR; split_ifs
  · exact measurable_id
  · exact measurable_const

theorem measurable_cupG (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (s : ℝ) (j : Fin 2) :
    Measurable fun u => cupG m inner ζ u s j := by
  unfold cupG; split_ifs
  · exact measurable_id
  · exact measurable_const

theorem norm_cutPh (m : MiniTreeCode) (ζ : ℤˣ) (L γ δ : ℝ) {d : ℕ} (k : Mom d) (s : ℝ) (e : PairE m d) (u : ℝ) :
    ‖cutPh m ζ L γ δ k s e u‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem stronglyMeasurable_cutPh (m : MiniTreeCode) (ζ : ℤˣ) (L γ δ : ℝ) {d : ℕ} (k : Mom d) (s : ℝ)
    (e : PairE m d) : StronglyMeasurable (cutPh m ζ L γ δ k s e) := by
  unfold cutPh
  refine Continuous.stronglyMeasurable ?_
  fun_prop

theorem volume_cutU_ne_top (LG : LayeredGarden 1) (Xp : RegChain) (T s : ℝ) : volume (cutU LG Xp T s) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := volume (Ioo (layerAt LG ((0 : Fin 1), Xp.lonePath) : ℝ)
    (layerAt LG ((0 : Fin 1), Xp.lonePath) + 1))) ?_ (measure_mono fun u hu => ⟨hu.1, hu.2.1⟩)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}
variable (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
include D

/-! ### Input leaves of the pieces are input leaves of the protected tree -/

section Leaves

variable {GZ : Garden 1} (hZ : (cpair m Qr Qg inner).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
include hZ hsZ
variable {d : ℕ} (L : ℝ) (H : LeafProfiles 1 d)
  (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
include hH

theorem hH_P (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGp.garden,
    Summable fun n : Fin d → ℤ => |cutHp H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := (D.gd hZ hsZ).inputLeaf_ofTop D.decP.2.1 (D.hmtop hZ hsZ) ℓ hℓ
  have : cutHp H ℓ.1 = H ℓ'.1 := by rw [he]; rfl
  rw [this]
  exact hH ℓ' hℓ' k'

theorem hH_I (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGi.garden,
    Summable fun n : Fin d → ℤ => |cutHi Xp m H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ₁, hℓ₁, he₁⟩ := (D.hp hZ hsZ).inputLeaf_ofI ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := (D.gd hZ hsZ).inputLeaf_ofBot (D.hmbot hZ hsZ) ℓ₁ hℓ₁
  have : cutHi Xp m H ℓ.1 = H ℓ'.1 := by
    rw [he, he₁]; simp [cutHi, botAddr, pφi]
  rw [this]
  exact hH ℓ' hℓ' k'

theorem hH_R (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGr.garden,
    Summable fun n : Fin d → ℤ => |cutHr Xp m inner (LG.garden.sig 0) H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ₁, hℓ₁, he₁⟩ := (D.hp hZ hsZ).inputLeaf_ofR ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := (D.gd hZ hsZ).inputLeaf_ofBot (D.hmbot hZ hsZ) ℓ₁ hℓ₁
  have : cutHr Xp m inner (LG.garden.sig 0) H ℓ.1 = H ℓ'.1 := by
    rw [he, he₁]; simp [cutHr, botAddr, pφr, hsZ]
  rw [this]
  exact hH ℓ' hℓ' k'

theorem hH_G (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGg.garden,
    Summable fun n : Fin d → ℤ => |cutHg Xp m inner (LG.garden.sig 0) H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ₁, hℓ₁, he₁⟩ := (D.hp hZ hsZ).inputLeaf_ofG ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := (D.gd hZ hsZ).inputLeaf_ofBot (D.hmbot hZ hsZ) ℓ₁ hℓ₁
  have : cutHg Xp m inner (LG.garden.sig 0) H ℓ.1 = H ℓ'.1 := by
    rw [he, he₁]; simp [cutHg, botAddr, pφg, hsZ]
  rw [this]
  exact hH ℓ' hℓ' k'

end Leaves

/-! ### The kernel identity -/

/-- **(cut-term), o73 Prop 13.1 on `kernelProt`** (milestone MK-α). -/
theorem kernelProt_cutTerm (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mp : (GNode LGp.garden.tree → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mp Mi Mr Mg) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMp : ∀ K, ‖Mp K‖ ≤ CM)
    (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (T s s' : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (termFix Xp m inner s) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s e u *
            (kernelProt L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                    (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
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
  have hS : ∀ q, protSummand L γ δ LG H M (fun _ => T) s' (termFix Xp m inner s) k (Φ.symm q) =
      (Mc (starA m L k q.2.1) (starB m L k q.2.1) * (cutEps m q.2.1 : ℂ)) *
        ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s q.2.1 u *
          (protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k q.1 *
            (protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun _ => none)
                (k + latticePoint L q.2.1.1.1) q.2.2.1 *
              (protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.1) q.2.2.2.1 *
                protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.2) q.2.2.2.2))) := by
    intro q
    have := D.summand_eq hZ hsZ (Φ.symm q) L γ δ H M Mc Mp Mi Mr Mg hM T s s' k
    rw [Φ.apply_symm_apply] at this
    exact this
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun _ => T) s' (termFix Xp m inner s) k
    (card_lone_le_of_decodesTree D.dec) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun _ => T) s' (termFix Xp m inner s) k (Φ.symm q) :=
    ((Φ.symm.summable_iff).mpr hsumG.of_norm)
  rw [tsum_cut_assembly (cutU LG Xp T s) (volume_cutU_ne_top LG Xp T s)
    (fun e => Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ))
    (fun e u => cutPh m (LG.garden.sig 0) L γ δ k s e u)
    (fun e u => (norm_cutPh m _ L γ δ k s e u).le) (fun e => stronglyMeasurable_cutPh m _ L γ δ k s e)
    (fun p u => protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k p)
    (fun e i u => protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun _ => none)
      (k + latticePoint L e.1.1) i)
    (fun e r u => protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
      (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r)
    (fun e g u => protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
      (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g)
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
                  (fun _ => none) (k + latticePoint L e.1.1) i) *
                  ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0, protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r) *
                    (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0, protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s e u *
              ((∑' p : GenDecoration LGp.garden d (fun _ => 0) 0, protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k p) *
                ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0, protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s
                  (fun _ => none) (k + latticePoint L e.1.1) i) *
                  ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0, protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r) *
                    (∑' g : GenDecoration LGg.garden d (fun _ => 0) 0, protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g))))) := by
    intro e
    have hu : ∀ u, cutPh m (LG.garden.sig 0) L γ δ k s e u *
              ((c ^ LGp.garden.order * LGp.garden.zeta * ∑' p : GenDecoration LGp.garden d (fun _ => 0) 0, protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k p) *
                ((c ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0, protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s
                  (fun _ => none) (k + latticePoint L e.1.1) i) *
                  ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0, protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r) *
                    (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0, protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (cutPh m (LG.garden.sig 0) L γ δ k s e u *
              ((∑' p : GenDecoration LGp.garden d (fun _ => 0) 0, protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k p) *
                ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0, protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s
                  (fun _ => none) (k + latticePoint L e.1.1) i) *
                  ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0, protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r) *
                    (∑' g : GenDecoration LGg.garden d (fun _ => 0) 0, protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g))))) := fun u => by ring
    simp_rw [hu, integral_const_mul]
    ring
  rw [tsum_congr hpull, tsum_mul_left, hord, hzeta, pow_add]
  ring

end CutTermData

end WaveTurbulence.Flower.ProtCut
