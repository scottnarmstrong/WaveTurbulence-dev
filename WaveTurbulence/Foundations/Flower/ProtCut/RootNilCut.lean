/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootNilKer

/-! # D2c PROT-CUT, MK-β: one-pair chains on `kernelProt` — (P2) and the root cut without suffix

For a protected tree with code `X = pair m Qr Qg inner nil` (`PairOnly`):

* **`PairOnly.kernelProt_both`** ((P2), `ProtCfg.rootTerm`: root at `σ`, terminal `𝔫_b` at `v`):
  `kernelProt = c² (iζ_a)(iζ_b) Σ'_e c_e e^{πiA_e(σ−v)} K_int(σ, v) Q_r(σ, v) Q_g(σ, v)`;
* **`PairOnly.kernelProt_root0`** ((P1)/(trace) when `rest = nil`):
  `kernelProt (root at σ) = c² (iζ_a)(iζ_b) Σ'_e c_e ∫_{rootU0} e^{πiA_e(σ−u)} K_int(σ, u) Q_r(σ, u) Q_g(σ, u) du`
  with `rootU0 = {max(𝔏_b, 0, s) < u < min(𝔏_b + 1, T, σ)}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The bookkeeping of a cut with both linked nodes designated (no integral). -/
theorem tsum_pair_assembly {E Di Dr Dg : Type*} (c : E → ℂ) (Si : E → Di → ℂ) (Sr : E → Dr → ℂ)
    (Sg : E → Dg → ℂ) (nSi : ∀ e, Summable fun i => ‖Si e i‖) (nSr : ∀ e, Summable fun r => ‖Sr e r‖)
    (nSg : ∀ e, Summable fun g => ‖Sg e g‖) (S : E × (Di × (Dr × Dg)) → ℂ)
    (hS : ∀ q, S q = c q.1 * (Si q.1 q.2.1 * (Sr q.1 q.2.2.1 * Sg q.1 q.2.2.2))) (hsum : Summable S) :
    ∑' q, S q = ∑' e, c e * ((∑' i, Si e i) * ((∑' r, Sr e r) * ∑' g, Sg e g)) := by
  have hslice : ∀ e, Summable fun r : Di × (Dr × Dg) => S (e, r) := by
    intro e
    have n3 := (nSi e).mul_norm ((nSr e).mul_norm (nSg e))
    simp only [hS]
    exact (n3.of_norm.mul_left (c e))
  rw [Summable.tsum_prod' hsum hslice]
  refine tsum_congr fun e => ?_
  simp only [hS]
  rw [tsum_mul_left]
  congr 1
  rw [tsum_mul_tsum_of_summable_norm (nSr e) (nSg e),
    tsum_mul_tsum_of_summable_norm (nSi e) ((nSr e).mul_norm (nSg e))]

namespace PairOnly

variable {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg)
include D

section Leaves

variable {d : ℕ} (L : ℝ) (H : LeafProfiles 1 d)
  (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
include hH

theorem hH_I (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGi.garden,
    Summable fun n : Fin d → ℤ => |cutHi .nil m H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := D.hp.inputLeaf_ofI ℓ hℓ
  have : cutHi .nil m H ℓ.1 = H ℓ'.1 := by rw [he]; simp [cutHi, pφi, RegChain.lonePath]
  rw [this]
  exact hH ℓ' hℓ' k'

theorem hH_R (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGr.garden,
    Summable fun n : Fin d → ℤ => |cutHr .nil m inner (LG.garden.sig 0) H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := D.hp.inputLeaf_ofR ℓ hℓ
  have : cutHr .nil m inner (LG.garden.sig 0) H ℓ.1 = H ℓ'.1 := by rw [he]; simp [cutHr, pφr, RegChain.lonePath]
  rw [this]
  exact hH ℓ' hℓ' k'

theorem hH_G (k' : Mom d) : ∀ ℓ ∈ inputLeaves LGg.garden,
    Summable fun n : Fin d → ℤ => |cutHg .nil m inner (LG.garden.sig 0) H ℓ.1 (k' + latticePoint L n)| := by
  intro ℓ hℓ
  obtain ⟨ℓ', hℓ', he⟩ := D.hp.inputLeaf_ofG ℓ hℓ
  have : cutHg .nil m inner (LG.garden.sig 0) H ℓ.1 = H ℓ'.1 := by rw [he]; simp [cutHg, pφg, RegChain.lonePath]
  rw [this]
  exact hH ℓ' hℓ' k'

end Leaves

theorem order_eq : LG.garden.order = LGi.garden.order + LGr.garden.order + LGg.garden.order + 2 :=
  D.hp.order_pair

theorem zeta_eq : LG.garden.zeta = (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
    (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
      (LGi.garden.zeta * (LGr.garden.zeta * LGg.garden.zeta)) := by
  rw [D.hp.zeta_pair]
  have sa : LG.garden.sign D.hp.rootB.toNode = LG.garden.sig 0 := by
    show pathSign (LG.garden.sig 0) [] = _
    simp [pathSign]
  have sb : LG.garden.sign D.hp.bB.toNode = slotSign (LG.garden.sig 0) m.c := by
    show pathSign (LG.garden.sig 0) (bPath m inner) = _
    rw [bPath, Comb.pathSign_append, pathSign_singleton, lonePath_sign]
  rw [sa, sb]

/-- **(P2) on `kernelProt`**: both linked nodes of a one-pair protected tree designated. -/
theorem kernelProt_both (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (hM : D.MultFactors M Mc Mi Mr Mg) (CM : ℝ)
    (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM)
    (T s σ v : ℝ) (hσT : σ ≤ T) (hvT : v ≤ T) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s (pairFix m inner σ v) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          (cutPh m (LG.garden.sig 0) L γ δ k v e σ *
            (kernelProt L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) v (fun _ => none)
                (k + latticePoint L e.1.1) (fun _ => 0) 0 *
              (kernelProt L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                kernelProt L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hMi 0)
  have hMb : ∀ K, ‖M K‖ ≤ CM * (CM * (CM * CM)) := by
    intro K
    rw [hM K, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact hMc _ _
    · exact hMi _
    · exact hMr _
    · exact hMg _
  set Φ := D.hp.decEquiv d
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hS : ∀ q, protSummand L γ δ LG H M (fun _ => T) s (pairFix m inner σ v) k (Φ.symm q) =
      (Mc (starA m L k q.1) (starB m L k q.1) * (cutEps m q.1 : ℂ) * cutPh m (LG.garden.sig 0) L γ δ k v q.1 σ) *
        (protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) v (fun _ => none)
            (k + latticePoint L q.1.1.1) q.2.1 *
          (protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
              (fun y => cupR m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
              (k + latticePoint L q.1.1.2.1) q.2.2.1 *
            protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
              (fun y => cupG m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
              (k + latticePoint L q.1.1.2.2) q.2.2.2)) := by
    intro q
    have := D.summand_both (Φ.symm q) L γ δ H M Mc Mi Mr Mg hM T s σ v hσT hvT k
    rw [Φ.apply_symm_apply] at this
    rw [this]
    ring
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun _ => T) s (pairFix m inner σ v) k
    (card_lone_le_of_decodesTree D.dec) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun _ => T) s (pairFix m inner σ v) k (Φ.symm q) :=
    (Φ.symm.summable_iff).mpr hsumG.of_norm
  rw [tsum_pair_assembly
    (fun e => Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) * cutPh m (LG.garden.sig 0) L γ δ k v e σ)
    (fun e i => protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) v (fun _ => none)
      (k + latticePoint L e.1.1) i)
    (fun e r => protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
      (fun y => cupR m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r)
    (fun e g => protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
      (fun y => cupG m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g)
    (fun e => summable_protSummand_norm L γ δ LGi _ Mi CM hMi _ _ _ _ (card_lone_le_of_decodesTree D.decI)
      (fun ℓ hℓ => D.hH_I L H hH _ ℓ hℓ))
    (fun e => summable_protSummand_norm L γ δ LGr _ Mr CM hMr _ _ _ _ (card_lone_le_of_plain D.decR.1.1)
      (fun ℓ hℓ => D.hH_R L H hH _ ℓ hℓ))
    (fun e => summable_protSummand_norm L γ δ LGg _ Mg CM hMg _ _ _ _ (card_lone_le_of_plain D.decG.1.1)
      (fun ℓ hℓ => D.hH_G L H hH _ ℓ hℓ)) _ hS hsum]
  simp only [kernelProt_eq_tsum]
  set c := (coupling d L γ δ : ℂ)
  set C₀ := c ^ LGi.garden.order * LGi.garden.zeta *
    (c ^ LGr.garden.order * LGr.garden.zeta * (c ^ LGg.garden.order * LGg.garden.zeta))
  have hpull : ∀ e : PairE m d,
      Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
        (cutPh m (LG.garden.sig 0) L γ δ k v e σ *
          ((c ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
              protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) v (fun _ => none) (k + latticePoint L e.1.1) i) *
            ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
              protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                (fun y => cupR m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
                (k + latticePoint L e.1.2.1) r) *
              (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) * cutPh m (LG.garden.sig 0) L γ δ k v e σ *
          ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
              protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) v (fun _ => none) (k + latticePoint L e.1.1) i) *
            ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
              protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                (fun y => cupR m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
                (k + latticePoint L e.1.2.1) r) *
              ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) g))) := fun e => by ring
  rw [tsum_congr hpull, tsum_mul_left, D.order_eq, D.zeta_eq, pow_add, pow_add, pow_add]
  ring

/-- **The root cut of a one-pair protected tree on `kernelProt`** ((P1)/(trace) with `rest = nil`). -/
theorem kernelProt_root0 (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (hM : D.MultFactors M Mc Mi Mr Mg) (CM : ℝ)
    (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM)
    (T s σ : ℝ) (hσT : σ ≤ T) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s (rootFix σ) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in rootU0 LG m inner T σ s, cutPh m (LG.garden.sig 0) L γ δ k u e σ *
            (kernelProt L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                (k + latticePoint L e.1.1) (fun _ => 0) 0 *
              (kernelProt L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                kernelProt L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) (fun _ => 0) 0)) := by
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hMi 0)
  have hMb : ∀ K, ‖M K‖ ≤ CM * (CM * (CM * CM)) := by
    intro K
    rw [hM K, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact hMc _ _
    · exact hMi _
    · exact hMr _
    · exact hMg _
  set Φ := (D.hp.decEquiv d).trans ((Equiv.punitProd _).symm : _ ≃ Unit × _)
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hΦ : ∀ q, D.hp.decEquiv d (Φ.symm q) = q.2 := fun q => by
    simp only [Φ, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    rfl
  have hS : ∀ q, protSummand L γ δ LG H M (fun _ => T) s (rootFix σ) k (Φ.symm q) =
      (Mc (starA m L k q.2.1) (starB m L k q.2.1) * (cutEps m q.2.1 : ℂ)) *
        ∫ u in rootU0 LG m inner T σ s, cutPh m (LG.garden.sig 0) L γ δ k u q.2.1 σ *
          ((fun (_ : Unit) (_ : ℝ) => (1 : ℂ)) q.1 u *
            (protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                (k + latticePoint L q.2.1.1.1) q.2.2.1 *
              (protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.1) q.2.2.2.1 *
                protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.2) q.2.2.2.2))) := by
    intro q
    have := D.summand_root0 (Φ.symm q) L γ δ H M Mc Mi Mr Mg hM T s σ hσT k
    rw [hΦ] at this
    exact this
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun _ => T) s (rootFix σ) k
    (card_lone_le_of_decodesTree D.dec) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun _ => T) s (rootFix σ) k (Φ.symm q) :=
    (Φ.symm.summable_iff).mpr hsumG.of_norm
  rw [tsum_cut_assembly (rootU0 LG m inner T σ s) (volume_rootU0_ne_top LG m inner T σ s)
    (fun e => Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ))
    (fun e u => cutPh m (LG.garden.sig 0) L γ δ k u e σ)
    (fun e u => (norm_cutPh m _ L γ δ k u e σ).le) (fun e => stronglyMeasurable_cutPh₂ m _ L γ δ k e σ)
    (fun (_ : Unit) (_ : ℝ) => (1 : ℂ))
    (fun e i u => protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
      (k + latticePoint L e.1.1) i)
    (fun e r u => protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
      (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.1) r)
    (fun e g u => protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
      (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2) g)
    (fun _ => 1)
    (fun e i => CM * leafMajorant L LGi (cutHi .nil m H) (k + latticePoint L e.1.1) i)
    (fun e r => CM * leafMajorant L LGr (cutHr .nil m inner (LG.garden.sig 0) H) (k + latticePoint L e.1.2.1) r)
    (fun e g => CM * leafMajorant L LGg (cutHg .nil m inner (LG.garden.sig 0) H) (k + latticePoint L e.1.2.2) g)
    (fun _ _ => by simp)
    (fun e i u => norm_protSummand_le L γ δ _ _ _ CM hMi _ _ _ _ i)
    (fun e r u => norm_protSummand_le L γ δ _ _ _ CM hMr _ _ _ _ r)
    (fun e g u => norm_protSummand_le L γ δ _ _ _ CM hMg _ _ _ _ g)
    (hasSum_fintype _).summable
    (fun e => (summable_leafMajorant L LGi (cutHi .nil m H) (k + latticePoint L e.1.1) (fun _ => 0) 0
      (card_lone_le_of_decodesTree D.decI) (D.hH_I L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LGr _ (k + latticePoint L e.1.2.1) (fun _ => 0) 0
      (card_lone_le_of_plain D.decR.1.1) (D.hH_R L H hH _)).mul_left CM)
    (fun e => (summable_leafMajorant L LGg _ (k + latticePoint L e.1.2.2) (fun _ => 0) 0
      (card_lone_le_of_plain D.decG.1.1) (D.hH_G L H hH _)).mul_left CM)
    (fun _ => stronglyMeasurable_const)
    (fun e i => stronglyMeasurable_protSummand L γ δ LGi _ Mi (fun _ _ => σ) id _ _
      (fun _ => measurable_const) measurable_id i)
    (fun e r => stronglyMeasurable_protSummand L γ δ LGr _ Mr
      (fun u y => cupR m inner (LG.garden.sig 0) σ u y.1.1) (fun _ => 0) _ _
      (fun y => measurable_cupR₂ m inner _ σ y.1.1) measurable_const r)
    (fun e g => stronglyMeasurable_protSummand L γ δ LGg _ Mg
      (fun u y => cupG m inner (LG.garden.sig 0) σ u y.1.1) (fun _ => 0) _ _
      (fun y => measurable_cupG₂ m inner _ σ y.1.1) measurable_const g)
    _ hS hsum]
  have h1 : (∑' _ : Unit, (1 : ℂ)) = 1 := by simp
  simp only [h1, one_mul, kernelProt_eq_tsum]
  set c := (coupling d L γ δ : ℂ)
  set C₀ := c ^ LGi.garden.order * LGi.garden.zeta *
    (c ^ LGr.garden.order * LGr.garden.zeta * (c ^ LGg.garden.order * LGg.garden.zeta))
  have hpull : ∀ e : PairE m d,
      Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
        ∫ u in rootU0 LG m inner T σ s, cutPh m (LG.garden.sig 0) L γ δ k u e σ *
          ((c ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
              protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none) (k + latticePoint L e.1.1) i) *
            ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
              protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                (k + latticePoint L e.1.2.1) r) *
              (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) g))) =
        C₀ * (Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in rootU0 LG m inner T σ s, cutPh m (LG.garden.sig 0) L γ δ k u e σ *
            ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
                protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                  (k + latticePoint L e.1.1) i) *
              ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
                protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) r) *
                ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) g))) := by
    intro e
    have hu : ∀ u, cutPh m (LG.garden.sig 0) L γ δ k u e σ *
          ((c ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
              protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none) (k + latticePoint L e.1.1) i) *
            ((c ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
              protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                (k + latticePoint L e.1.2.1) r) *
              (c ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) g))) =
        C₀ * (cutPh m (LG.garden.sig 0) L γ δ k u e σ *
            ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
                protSummand L γ δ LGi (cutHi .nil m H) Mi (fun _ => σ) u (fun _ => none)
                  (k + latticePoint L e.1.1) i) *
              ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
                protSummand L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) r) *
                ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) g))) := fun u => by ring
    simp_rw [hu, integral_const_mul]
    ring
  rw [tsum_congr hpull, tsum_mul_left, D.order_eq, D.zeta_eq, pow_add, pow_add, pow_add]
  ring

end PairOnly

end WaveTurbulence.Flower.ProtCut
