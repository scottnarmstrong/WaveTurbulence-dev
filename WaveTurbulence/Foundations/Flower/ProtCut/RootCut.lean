/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootSummand

/-! # D2c PROT-CUT, milestone MK-β: the root cut (o104 Prop 7.4 (a) with §13.1; (P1); (trace))

For a protected paired tree `LG` with code `X = pair m Qr Qg inner rest` (`rest ≠ nil`), with the root designated at
`σ ≤ T`, output `k` and lone-port time `s`:

`kernelProt LG (root at σ) = c² (iζ_a)(iζ_b) Σ'_{e ∈ PairE} c_e ∫_{rootU} e^{πiA_e(σ−u)}
    K_suf(u, s) K_int(σ, u) Q_r(σ, u) Q_g(σ, u) du`   (**`RootData.kernelProt_rootCut`**)

* the pieces are unpinned `kernelProt`s of the suffix `LGs` (code `rest`, upper clock `u`, lone-port time `s`), the
  interior `LGi` (code `inner`, upper clock `σ`, lone-port time `u`) and the side couples `LGr`, `LGg` (upper clocks
  `σ` at the root and `u` at `𝔫_b`);
* their outputs `k`, `k + e.x/L`, `k + e.yr/L`, `k + e.yg/L` are affine in `(k, e)`;
* the multiplier factors (`RootData.MultFactors`), `c_e = M_cut(star_a, star_b) ε_a ε_b`, `A_e = ζ δ L^{2γ} Ω_{𝔫_1}`;
* `rootU = {max(𝔏_b, 0) < u < min(𝔏_b + 1, T, σ)}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

theorem measurable_cupR₂ (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (σ : ℝ) (j : Fin 2) :
    Measurable fun u => cupR m inner ζ σ u j := by
  unfold cupR; split_ifs
  · exact measurable_const
  · exact measurable_id

theorem measurable_cupG₂ (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (σ : ℝ) (j : Fin 2) :
    Measurable fun u => cupG m inner ζ σ u j := by
  unfold cupG; split_ifs
  · exact measurable_const
  · exact measurable_id

theorem stronglyMeasurable_cutPh₂ (m : MiniTreeCode) (ζ : ℤˣ) (L γ δ : ℝ) {d : ℕ} (k : Mom d)
    (e : PairE m d) (σ : ℝ) : StronglyMeasurable fun u => cutPh m ζ L γ δ k u e σ := by
  unfold cutPh
  refine Continuous.stronglyMeasurable ?_
  fun_prop

theorem volume_rootU_ne_top (LG : LayeredGarden 1) (m : MiniTreeCode) (inner : RegChain) (T σ : ℝ) :
    volume (rootU LG m inner T σ) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := volume (Ioo (layerAt LG ((0 : Fin 1), bPath m inner) : ℝ)
    (layerAt LG ((0 : Fin 1), bPath m inner) + 1))) ?_ (measure_mono fun u hu => ⟨hu.1, hu.2.1⟩)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

namespace RootData

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
include D

/-- **The root pin at one decoration** (summand level). -/
theorem summand_root {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L γ δ : ℝ) (H : LeafProfiles 1 d)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (Ms : (GNode LGs.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mi Mr Mg Ms) (T s σ : ℝ) (hσT : σ ≤ T) (k : Mom d) :
    protSummand L γ δ LG H M (fun _ => T) s (rootFix σ) k κ =
      (Mc (starA m L k (D.Φr d κ).2.1) (starB m L k (D.Φr d κ).2.1) * (cutEps m (D.Φr d κ).2.1 : ℂ)) *
        ∫ u in rootU LG m inner T σ, cutPh m (LG.garden.sig 0) L γ δ k u (D.Φr d κ).2.1 σ *
          (protSummand L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k (D.Φr d κ).1 *
            (protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                (k + latticePoint L (D.Φr d κ).2.1.1.1) (D.Φr d κ).2.2.1 *
              (protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L (D.Φr d κ).2.1.1.2.1) (D.Φr d κ).2.2.2.1 *
                protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L (D.Φr d κ).2.1.1.2.2) (D.Φr d κ).2.2.2.2))) := by
  have hI : cosetDecoration LG.garden L k κ.1 ∘ (D.gd.ι₁ ∘ D.hp.ιi) =
      cosetDecoration LGi.garden L (k + latticePoint L (D.Φr d κ).2.1.1.1) ((D.Φr d κ).2.2.1).1 :=
    D.coset_I κ L k
  have hR : cosetDecoration LG.garden L k κ.1 ∘ (D.gd.ι₁ ∘ D.hp.ιr) =
      cosetDecoration LGr.garden L (k + latticePoint L (D.Φr d κ).2.1.1.2.1) ((D.Φr d κ).2.2.2.1).1 :=
    D.coset_R κ L k
  have hG : cosetDecoration LG.garden L k κ.1 ∘ (D.gd.ι₁ ∘ D.hp.ιg) =
      cosetDecoration LGg.garden L (k + latticePoint L (D.Φr d κ).2.1.1.2.2) ((D.Φr d κ).2.2.2.2).1 :=
    D.coset_G κ L k
  have hS : cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₂ = cosetDecoration LGs.garden L k ((D.Φr d κ).1).1 := rfl
  have hphase : ∀ u, Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode LGZ.garden (cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₁) D.hp.rootB * σ : ℝ) * Complex.I) *
      Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode LGZ.garden (cosetDecoration LG.garden L k κ.1 ∘ D.gd.ι₁) D.hp.bB * u : ℝ) * Complex.I) =
      cutPh m (LG.garden.sig 0) L γ δ k u (D.Φr d κ).2.1 σ := fun u => D.phase_root κ L k γ δ σ u
  unfold protSummand
  rw [hM, D.starA_eq κ L k, D.starB_eq κ L k, D.coset_S κ L k, D.coset_I κ L k, D.coset_R κ L k,
    D.coset_G κ L k, D.epsDec_root κ, D.protTime_rootCut L γ δ T s σ hσT (cosetDecoration LG.garden L k κ.1),
    D.prodH_root κ L k H]
  simp only [Function.comp_assoc, hI, hR, hG, hS, hphase]
  rw [show (LGZ.garden.sig 0) = LG.garden.sig 0 from D.sigZ]
  rw [show ∀ (a b c J : ℂ), a * (b * J * c) = (a * b * c) * J from fun a b c J => by ring]
  conv_lhs => rw [← integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  congr 1
  funext u
  push_cast
  ring

/-! ### Input leaves of the pieces -/

section Leaves

variable {d : ℕ} (L : ℝ) (H : LeafProfiles 1 d)
  (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
include hH

theorem hH_S (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGs.garden,
    Summable fun n : Fin d → ℤ => |rootHs m inner H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofBot D.hmbot ℓ hℓ
  have : rootHs m inner H ℓ.1 = H ℓ'.1 := by
    rw [he, cpair_lonePath]
    have hj : ℓ.1.1 = 0 := Subsingleton.elim _ _
    simp [rootHs, botAddr, hj]
  rw [this]
  exact hH ℓ' hℓ' k'

theorem hH_I (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGi.garden,
    Summable fun n : Fin d → ℤ => |cutHi .nil m H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ₁, hℓ₁, he₁⟩ := D.hp.inputLeaf_ofI ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofTop D.decZ.2.1 D.hmtop ℓ₁ hℓ₁
  have : cutHi .nil m H ℓ.1 = H ℓ'.1 := by
    rw [he, he₁]; simp [cutHi, topAddr, pφi, RegChain.lonePath]
  rw [this]
  exact hH ℓ' hℓ' k'

theorem hH_R (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGr.garden,
    Summable fun n : Fin d → ℤ => |cutHr .nil m inner (LG.garden.sig 0) H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ₁, hℓ₁, he₁⟩ := D.hp.inputLeaf_ofR ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofTop D.decZ.2.1 D.hmtop ℓ₁ hℓ₁
  have : cutHr .nil m inner (LG.garden.sig 0) H ℓ.1 = H ℓ'.1 := by
    rw [he, he₁]; simp [cutHr, topAddr, pφr, RegChain.lonePath, D.sigZ]
  rw [this]
  exact hH ℓ' hℓ' k'

theorem hH_G (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGg.garden,
    Summable fun n : Fin d → ℤ => |cutHg .nil m inner (LG.garden.sig 0) H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ₁, hℓ₁, he₁⟩ := D.hp.inputLeaf_ofG ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := D.gd.inputLeaf_ofTop D.decZ.2.1 D.hmtop ℓ₁ hℓ₁
  have : cutHg .nil m inner (LG.garden.sig 0) H ℓ.1 = H ℓ'.1 := by
    rw [he, he₁]; simp [cutHg, topAddr, pφg, RegChain.lonePath, D.sigZ]
  rw [this]
  exact hH ℓ' hℓ' k'

end Leaves

/-- **The root cut on `kernelProt`** (o104 Prop 7.4 (a), §13.1; (P1), (trace)). -/
theorem kernelProt_rootCut (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (Ms : (GNode LGs.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mi Mr Mg Ms) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM)
    (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (hMs : ∀ K, ‖Ms K‖ ≤ CM)
    (T s σ : ℝ) (hσT : σ ≤ T) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s (rootFix σ) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in rootU LG m inner T σ, cutPh m (LG.garden.sig 0) L γ δ k u e σ *
            (kernelProt L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                    (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hMs 0)
  have hMb : ∀ K, ‖M K‖ ≤ CM * (CM * (CM * (CM * CM))) := by
    intro K
    rw [hM K, norm_mul, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact hMc _ _
    · exact hMs _
    · exact hMi _
    · exact hMr _
    · exact hMg _
  set Φ := D.Φr d
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hS : ∀ q, protSummand L γ δ LG H M (fun _ => T) s (rootFix σ) k (Φ.symm q) =
      (Mc (starA m L k q.2.1) (starB m L k q.2.1) * (cutEps m q.2.1 : ℂ)) *
        ∫ u in rootU LG m inner T σ, cutPh m (LG.garden.sig 0) L γ δ k u q.2.1 σ *
          (protSummand L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k q.1 *
            (protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                (k + latticePoint L q.2.1.1.1) q.2.2.1 *
              (protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.1) q.2.2.2.1 *
                protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.2) q.2.2.2.2))) := by
    intro q
    have := D.summand_root (Φ.symm q) L γ δ H M Mc Mi Mr Mg Ms hM T s σ hσT k
    rw [Φ.apply_symm_apply] at this
    exact this
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun _ => T) s (rootFix σ) k
    (card_lone_le_of_decodesTree D.dec) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun _ => T) s (rootFix σ) k (Φ.symm q) :=
    ((Φ.symm.summable_iff).mpr hsumG.of_norm)
  rw [tsum_cut_assembly (rootU LG m inner T σ) (volume_rootU_ne_top LG m inner T σ)
    (fun e => Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ))
    (fun e u => cutPh m (LG.garden.sig 0) L γ δ k u e σ)
    (fun e u => (norm_cutPh m _ L γ δ k u e σ).le) (fun e => stronglyMeasurable_cutPh₂ m _ L γ δ k e σ)
    (fun p u => protSummand L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k p)
    (fun e i u => protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
      (k + latticePoint L e.1.1) i)
    (fun e r u => protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
      (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r)
    (fun e g u => protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
      (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g)
    (fun p => CM * leafMajorant L LGs (rootHs m inner H) k p)
    (fun e i => CM * leafMajorant L LGi (cutHi .nil m H) (k + latticePoint L e.1.1) i)
    (fun e r => CM * leafMajorant L LGr (cutHr .nil m inner (LG.garden.sig 0) H) (k + latticePoint L e.1.2.1) r)
    (fun e g => CM * leafMajorant L LGg (cutHg .nil m inner (LG.garden.sig 0) H) (k + latticePoint L e.1.2.2) g)
    (fun p u => norm_protSummand_le L γ δ _ _ _ CM hMs _ _ _ _ p)
    (fun e i u => norm_protSummand_le L γ δ _ _ _ CM hMi _ _ _ _ i)
    (fun e r u => norm_protSummand_le L γ δ _ _ _ CM hMr _ _ _ _ r)
    (fun e g u => norm_protSummand_le L γ δ _ _ _ CM hMg _ _ _ _ g)
    ((summable_leafMajorant L LGs (rootHs m inner H) k (fun _ => 0) 0 (card_lone_le_of_decodesTree D.decS)
      (D.hH_S L H hH k)).mul_left CM)
    (fun e => (summable_leafMajorant L LGi (cutHi .nil m H) (k + latticePoint L e.1.1) (fun _ => 0) 0
      (card_lone_le_of_decodesTree D.decI) (D.hH_I L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LGr _ (k + latticePoint L e.1.2.1) (fun _ => 0) 0
      (card_lone_le_of_plain D.decR.1.1) (D.hH_R L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LGg _ (k + latticePoint L e.1.2.2) (fun _ => 0) 0
      (card_lone_le_of_plain D.decG.1.1) (D.hH_G L H hH _)).mul_left CM)
    (fun p => stronglyMeasurable_protSummand L γ δ LGs _ Ms (fun u _ => u) (fun _ => s) _ k
      (fun _ => measurable_id) measurable_const p)
    (fun e i => stronglyMeasurable_protSummand L γ δ LGi _ Mi (fun _ _ => σ) id _ _
      (fun _ => measurable_const) measurable_id i)
    (fun e r => stronglyMeasurable_protSummand L γ δ LGr _ Mr
      (fun u y => cupR m inner (LG.garden.sig 0) σ u y.1.1) (fun _ => 0) _ _
      (fun y => measurable_cupR₂ m inner _ σ y.1.1) measurable_const r)
    (fun e g => stronglyMeasurable_protSummand L γ δ LGg _ Mg
      (fun u y => cupG m inner (LG.garden.sig 0) σ u y.1.1) (fun _ => 0) _ _
      (fun y => measurable_cupG₂ m inner _ σ y.1.1) measurable_const g)
    _ hS hsum]
  -- the constants
  have hord : LG.garden.order = LGs.garden.order + (LGi.garden.order + LGr.garden.order + LGg.garden.order + 2) := by
    rw [D.gd.order_glue, D.hp.order_pair]; ring
  have hzeta : LG.garden.zeta = LGs.garden.zeta * ((Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
      (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        (LGi.garden.zeta * (LGr.garden.zeta * LGg.garden.zeta))) := by
    rw [D.gd.zeta_glue, D.hp.zeta_pair]
    have sa : LGZ.garden.sign D.hp.rootB.toNode = LG.garden.sig 0 := by
      show pathSign (LGZ.garden.sig 0) [] = _
      simp [pathSign, D.sigZ]
    have sb : LGZ.garden.sign D.hp.bB.toNode = slotSign (LG.garden.sig 0) m.c := by
      show pathSign (LGZ.garden.sig 0) (bPath m inner) = _
      rw [bPath, Comb.pathSign_append, pathSign_singleton, lonePath_sign, D.sigZ]
    rw [sa, sb]
    ring
  simp only [kernelProt_eq_tsum]
  set c := (coupling d L γ δ : ℂ)
  set C₀ := c ^ LGs.garden.order * LGs.garden.zeta * (c ^ LGi.garden.order * LGi.garden.zeta *
    (c ^ LGr.garden.order * LGr.garden.zeta * (c ^ LGg.garden.order * LGg.garden.zeta)))
  have hpull : ∀ e : PairE m d,
      Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
        ∫ u in rootU LG m inner T σ, cutPh m (LG.garden.sig 0) L γ δ k u e σ *
              ((c ^ LGs.garden.order * LGs.garden.zeta * ∑' p : GenDecoration LGs.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k p) *
                ((c ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                    (k + latticePoint L e.1.1) i) *
                  ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
                    protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                      (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                      (k + latticePoint L e.1.2.1) r) *
                    (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                      protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                        (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                        (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in rootU LG m inner T σ, cutPh m (LG.garden.sig 0) L γ δ k u e σ *
              ((∑' p : GenDecoration LGs.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k p) *
                ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                    (k + latticePoint L e.1.1) i) *
                  ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
                    protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                      (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                      (k + latticePoint L e.1.2.1) r) *
                    (∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                      protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                        (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                        (k + latticePoint L e.1.2.2) g))))) := by
    intro e
    have hu : ∀ u, cutPh m (LG.garden.sig 0) L γ δ k u e σ *
              ((c ^ LGs.garden.order * LGs.garden.zeta * ∑' p : GenDecoration LGs.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k p) *
                ((c ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                    (k + latticePoint L e.1.1) i) *
                  ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
                    protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                      (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                      (k + latticePoint L e.1.2.1) r) *
                    (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                      protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                        (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                        (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (cutPh m (LG.garden.sig 0) L γ δ k u e σ *
              ((∑' p : GenDecoration LGs.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k p) *
                ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                    (k + latticePoint L e.1.1) i) *
                  ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
                    protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                      (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                      (k + latticePoint L e.1.2.1) r) *
                    (∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                      protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                        (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                        (k + latticePoint L e.1.2.2) g))))) := fun u => by ring
    simp_rw [hu, integral_const_mul]
    ring
  rw [tsum_congr hpull, tsum_mul_left, hord, hzeta, pow_add]
  ring

end RootData

end WaveTurbulence.Flower.ProtCut
