/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Root2Summand

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (a) for couples on `kernelProt` (`ε = +`)

For a couple `LG` decoded by `type2 (pair m Qr Qg inner rest) Xm Qlp` (`Root2Data`: closing pair `LGZ`, rest couple
`LGB = closeCouple rest Xm Qlp`; `PairOnly LGZ …`: interior `LGi`, side couples `LGr`, `LGg`), upper clocks `U`, and
the root of tree `0` designated at `σ ≤ U 0` (`trFix 0 σ`):

    kernelProt LG H M (U ·) s (trFix 0 σ) k = c² (iζ_a)(iζ_b) Σ'_{e ∈ PairE} Mc(star_a, star_b) ε_e
        ∫_{root2U} e^{πiA_e(σ−u)} K_rest(u, U 1)(k) · K_int(σ, u)(k + e.x/L) · Q_r(σ, u) Q_g(σ, u) du
                                                              (**`Root2Data.kernelProt_root2`**)

* `u = τ_{n_b}`, `root2U = {𝔏_b < u < 𝔏_b + 1, 0 < u, u < U 0, u < σ}` (o104 (a) with the couple's `lo = 𝔏_{ρ'}`,
  `hi = min(σ, 𝔏_{ρ'} + 1)`: a couple has no port);
* `K_rest` is the couple `closeCouple rest Xm Qlp` (o104's `P_4`) with its tree `0` below `n_b` (clock `u`) and its
  tree `1` (the chain `X⁻`) at its own clock `U 1` (`bClock`); `K_int` has upper clock `σ` and lone-port time `u`;
  the side couples have the clocks `cupR`/`cupG` (`σ` at `n_1`, `u` at `n_b`);
* `A_e = ζ_a δ L^{2γ} Ω_{n_1}` (`cutPh`), the same linked frequency as in the tree root cut; `ζ_a = +1`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace Root2Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D P

/-- **o104 Prop 7.4 (a) for couples on `kernelProt`** (the root of the nonempty `+` chain traced). -/
theorem kernelProt_root2 (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (MZ : (GNode LGZ.garden.tree → Mom d) → ℂ)
    (MB : (GNode LGB.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hMg : ∀ K, M K = MZ (K ∘ D.gd.ι₁) * MB (K ∘ D.gd.ι₂)) (hMZ : P.MultFactors MZ Mc Mi Mr Mg) (CM : ℝ)
    (hMB : ∀ K, ‖MB K‖ ≤ CM) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM)
    (hMgb : ∀ K, ‖Mg K‖ ≤ CM) (U : Fin 2 → ℝ) (s σ : ℝ) (hσ : σ ≤ U 0) (k : Mom d) :
    kernelProt L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LGZ.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LGZ.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in root2U LG m inner (U 0) σ, cutPh m (LGZ.garden.sig 0) L γ δ k u e σ *
            (kernelProt L γ δ LGB (t2HQ (cpair m Qr Qg inner) H) MB (fun y => bClock U u y.1.1) s
                (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi .nil m (t2HX H)) Mi (fun _ => σ) u (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr .nil m inner (LGZ.garden.sig 0) (t2HX H)) Mr
                    (fun y => cupR m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg .nil m inner (LGZ.garden.sig 0) (t2HX H)) Mg
                    (fun y => cupG m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hMi 0)
  have hMb : ∀ K, ‖M K‖ ≤ CM * (CM * (CM * (CM * CM))) := by
    intro K
    rw [hMg K, hMZ, norm_mul, norm_mul, norm_mul, norm_mul]
    calc _ ≤ CM * (CM * (CM * CM)) * CM := by
          gcongr
          · exact hMc _ _
          · exact hMi _
          · exact hMr _
          · exact hMgb _
          · exact hMB _
      _ = _ := by ring
  set HZ := t2HX H
  set HB := t2HQ (cpair m Qr Qg inner) H
  have hHZ := D.hH_Z L H hH
  set ζ := LGZ.garden.sig 0
  set Φ := D.Φ2 P d
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hS : ∀ q, protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k (Φ.symm q) =
      (Mc (starA m L k q.2.1) (starB m L k q.2.1) * (cutEps m q.2.1 : ℂ)) *
        ∫ u in root2U LG m inner (U 0) σ, cutPh m ζ L γ δ k u q.2.1 σ *
          (protSummand L γ δ LGB HB MB (fun y => bClock U u y.1.1) s (fun _ => none) k q.1 *
            (protSummand L γ δ LGi (cutHi .nil m HZ) Mi (fun _ => σ) u (fun _ => none)
                (k + latticePoint L q.2.1.1.1) q.2.2.1 *
              (protSummand L γ δ LGr (cutHr .nil m inner ζ HZ) Mr (fun y => cupR m inner ζ σ u y.1.1) 0
                  (fun _ => none) (k + latticePoint L q.2.1.1.2.1) q.2.2.2.1 *
                protSummand L γ δ LGg (cutHg .nil m inner ζ HZ) Mg (fun y => cupG m inner ζ σ u y.1.1) 0
                  (fun _ => none) (k + latticePoint L q.2.1.1.2.2) q.2.2.2.2))) := by
    intro q
    have := D.summand_root2 P (Φ.symm q) L γ δ k H M MZ MB Mc Mi Mr Mg hMg hMZ U s σ hσ
    rw [show D.Φ2 P d (Φ.symm q) = q from Φ.apply_symm_apply q] at this
    exact this
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun b => U b.1.1) s (trFix 0 σ) k
    (card_lone_le_of_plain D.plain) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k (Φ.symm q) :=
    (Φ.symm.summable_iff).mpr hsumG.of_norm
  rw [tsum_cut_assembly (root2U LG m inner (U 0) σ) (volume_root2U_ne_top LG m inner (U 0) σ)
    (fun e => Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ))
    (fun e u => cutPh m ζ L γ δ k u e σ)
    (fun e u => (norm_cutPh m _ L γ δ k u e σ).le) (fun e => stronglyMeasurable_cutPh₂ m _ L γ δ k e σ)
    (fun p u => protSummand L γ δ LGB HB MB (fun y => bClock U u y.1.1) s (fun _ => none) k p)
    (fun e i u => protSummand L γ δ LGi (cutHi .nil m HZ) Mi (fun _ => σ) u (fun _ => none)
      (k + latticePoint L e.1.1) i)
    (fun e r u => protSummand L γ δ LGr (cutHr .nil m inner ζ HZ) Mr (fun y => cupR m inner ζ σ u y.1.1) 0
      (fun _ => none) (k + latticePoint L e.1.2.1) r)
    (fun e g u => protSummand L γ δ LGg (cutHg .nil m inner ζ HZ) Mg (fun y => cupG m inner ζ σ u y.1.1) 0
      (fun _ => none) (k + latticePoint L e.1.2.2) g)
    (fun p => CM * leafMajorant L LGB HB k p)
    (fun e i => CM * leafMajorant L LGi (cutHi .nil m HZ) (k + latticePoint L e.1.1) i)
    (fun e r => CM * leafMajorant L LGr (cutHr .nil m inner ζ HZ) (k + latticePoint L e.1.2.1) r)
    (fun e g => CM * leafMajorant L LGg (cutHg .nil m inner ζ HZ) (k + latticePoint L e.1.2.2) g)
    (fun p u => norm_protSummand_le L γ δ _ _ _ CM hMB _ _ _ _ p)
    (fun e i u => norm_protSummand_le L γ δ _ _ _ CM hMi _ _ _ _ i)
    (fun e r u => norm_protSummand_le L γ δ _ _ _ CM hMr _ _ _ _ r)
    (fun e g u => norm_protSummand_le L γ δ _ _ _ CM hMgb _ _ _ _ g)
    ((summable_leafMajorant L LGB HB k (fun _ => 0) 0 (card_lone_le_of_plain D.plainB) (D.hH_B L H hH k)).mul_left CM)
    (fun e => (summable_leafMajorant L LGi (cutHi .nil m HZ) (k + latticePoint L e.1.1) (fun _ => 0) 0
      (card_lone_le_of_decodesTree P.decI) (P.hH_I L HZ hHZ _)).mul_left CM)
    (fun e => (summable_leafMajorant L LGr _ (k + latticePoint L e.1.2.1) (fun _ => 0) 0
      (card_lone_le_of_plain P.decR.1.1) (P.hH_R L HZ hHZ _)).mul_left CM)
    (fun e => (summable_leafMajorant L LGg _ (k + latticePoint L e.1.2.2) (fun _ => 0) 0
      (card_lone_le_of_plain P.decG.1.1) (P.hH_G L HZ hHZ _)).mul_left CM)
    (fun p => stronglyMeasurable_protSummand L γ δ LGB _ MB (fun u y => bClock U u y.1.1) (fun _ => s) _ _
      (fun y => measurable_bClock U y.1.1) measurable_const p)
    (fun e i => stronglyMeasurable_protSummand L γ δ LGi _ Mi (fun _ _ => σ) id _ _
      (fun _ => measurable_const) measurable_id i)
    (fun e r => stronglyMeasurable_protSummand L γ δ LGr _ Mr
      (fun u y => cupR m inner ζ σ u y.1.1) (fun _ => 0) _ _
      (fun y => measurable_cupR₂ m inner _ σ y.1.1) measurable_const r)
    (fun e g => stronglyMeasurable_protSummand L γ δ LGg _ Mg
      (fun u y => cupG m inner ζ σ u y.1.1) (fun _ => 0) _ _
      (fun y => measurable_cupG₂ m inner _ σ y.1.1) measurable_const g)
    _ hS hsum]
  simp only [kernelProt_eq_tsum]
  set cc := (coupling d L γ δ : ℂ)
  set C₀ := cc ^ LGB.garden.order * LGB.garden.zeta * (cc ^ LGi.garden.order * LGi.garden.zeta *
    (cc ^ LGr.garden.order * LGr.garden.zeta * (cc ^ LGg.garden.order * LGg.garden.zeta)))
  have hpull : ∀ e : PairE m d,
      Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
        ∫ u in root2U LG m inner (U 0) σ, cutPh m ζ L γ δ k u e σ *
          ((cc ^ LGB.garden.order * LGB.garden.zeta * ∑' p : GenDecoration LGB.garden d (fun _ => 0) 0,
              protSummand L γ δ LGB HB MB (fun y => bClock U u y.1.1) s (fun _ => none) k p) *
            ((cc ^ LGi.garden.order * LGi.garden.zeta * ∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
                protSummand L γ δ LGi (cutHi .nil m HZ) Mi (fun _ => σ) u (fun _ => none)
                  (k + latticePoint L e.1.1) i) *
              ((cc ^ LGr.garden.order * LGr.garden.zeta * ∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
                protSummand L γ δ LGr (cutHr .nil m inner ζ HZ) Mr (fun y => cupR m inner ζ σ u y.1.1) 0
                  (fun _ => none) (k + latticePoint L e.1.2.1) r) *
                (cc ^ LGg.garden.order * LGg.garden.zeta * ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGg (cutHg .nil m inner ζ HZ) Mg (fun y => cupG m inner ζ σ u y.1.1) 0
                    (fun _ => none) (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in root2U LG m inner (U 0) σ, cutPh m ζ L γ δ k u e σ *
            ((∑' p : GenDecoration LGB.garden d (fun _ => 0) 0,
                protSummand L γ δ LGB HB MB (fun y => bClock U u y.1.1) s (fun _ => none) k p) *
              ((∑' i : GenDecoration LGi.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGi (cutHi .nil m HZ) Mi (fun _ => σ) u (fun _ => none)
                    (k + latticePoint L e.1.1) i) *
                ((∑' r : GenDecoration LGr.garden d (fun _ => 0) 0,
                  protSummand L γ δ LGr (cutHr .nil m inner ζ HZ) Mr (fun y => cupR m inner ζ σ u y.1.1) 0
                    (fun _ => none) (k + latticePoint L e.1.2.1) r) *
                  ∑' g : GenDecoration LGg.garden d (fun _ => 0) 0,
                    protSummand L γ δ LGg (cutHg .nil m inner ζ HZ) Mg (fun y => cupG m inner ζ σ u y.1.1) 0
                      (fun _ => none) (k + latticePoint L e.1.2.2) g)))) := by
    intro e
    have key : ∀ (A C : ℂ) (f g : ℝ → ℂ), (∀ u, f u = C * g u) →
        A * (∫ u in root2U LG m inner (U 0) σ, f u) = C * (A * ∫ u in root2U LG m inner (U 0) σ, g u) := by
      intro A C f g hfg
      simp_rw [hfg, integral_const_mul]
      ring
    exact key _ _ _ _ (fun u => by beta_reduce; ring)
  rw [tsum_congr hpull, tsum_mul_left, D.gd.order_glue, P.order_eq, D.gd.zeta_glue, P.zeta_eq, pow_add,
    pow_add, pow_add, pow_add]
  ring

end Root2Data

end WaveTurbulence.Flower.ProtCut
