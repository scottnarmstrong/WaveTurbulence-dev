/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T2mSummand

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (c) on `kernelProt` — a type-2 couple with an empty chain (`ε = -`)

For a couple `LG` decoded by `type2 Xp nil (type1 c Q₁ Q₂ Q₃)` (`T2mData`: the chain `Xp` as a paired tree `LGX`, the
lone-pair couple `LGQ` and its sub-couples `LG₁ LG₂ LG₃` with the layers of `LG`), upper clocks `U`, and the root of
tree `1` designated at `σ ≤ U 1` (`trFix 1 σ`):

    kernelProt LG H M (U ·) s (trFix 1 σ) k = c² Σ'_{y ∈ T1E} Mc(stars) ε_y ∫_{t2mU} e^{πiB_y(σ−u)}
        K_X(U 0, port u)(k) · Q₁ Q₂ Q₃(σ_·(u))(k + y_·/L) du        (**`T2mData.kernelProt_t2m`**)

* `u` is the time of the partner `ρ'` (the root of the tree `0` of `Q_lp`, at `Xp.lonePath`),
  `t2mU = {𝔏_{ρ'} < u < 𝔏_{ρ'} + 1, 0 < u, u < U 0}`; o104 (c): the upper bound of `ρ'` is the time of `n⁺_{2m}`,
  carried by `K_X` (the chain as a paired tree with lone-port time `u`, o104's `K_{X^{−ε}}(·, u)`);
* `B_y = ζ₁ δ L^{2γ} Ω_y` with `ζ₁ = LGQ.garden.sig 1 = -1` (`t1Ph`), the phase of (b) for `Q_lp`;
* the sub-couples carry the clocks of the roots of `Q_lp` (`t1Clock 1 σ u`: `u` under `ρ'`, `σ` under `ρ`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace T2mData

variable {LG : LayeredGarden 2} {Xp : RegChain} {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl}
  {LGX : LayeredGarden 1} {LGQ : LayeredGarden 2} (D : T2mData LG Xp LGX LGQ)
  {LG₁ LG₂ LG₃ : LayeredGarden 2} (h : T1Data c Q₁ Q₂ Q₃ LGQ.garden LG₁.garden LG₂.garden LG₃.garden)
include D h

/-- **o104 Prop 7.4 (c) on `kernelProt`** (`ε = -`: the `-` chain empty, the root of tree `1` traced). -/
theorem kernelProt_t2m (hlA : ∀ z, LG₁.layer z = LGQ.layer (h.ιA z))
    (hlB : ∀ z, LG₂.layer z = LGQ.layer (h.ιB z)) (hlC : ∀ z, LG₃.layer z = LGQ.layer (h.ιC z))
    (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (MX : (GNode LGX.garden.tree → Mom d) → ℂ)
    (MQ : (GNode LGQ.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ) (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ)
    (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ)
    (hMg : ∀ K, M K = MX (K ∘ D.gd.ι₁) * MQ (K ∘ D.gd.ι₂)) (hMQ : h.MultFactors MQ Mc M₁ M₂ M₃) (CM : ℝ)
    (hMX : ∀ K, ‖MX K‖ ≤ CM) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hM₁ : ∀ K, ‖M₁ K‖ ≤ CM) (hM₂ : ∀ K, ‖M₂ K‖ ≤ CM)
    (hM₃ : ∀ K, ‖M₃ K‖ ≤ CM) (U : Fin 2 → ℝ) (s σ : ℝ) (hσ : σ ≤ U 1) (k : Mom d) :
    kernelProt L γ δ LG H M (fun b => U b.1.1) s (trFix 1 σ) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 *
        ∑' e : T1E d, Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
          ∫ u in t2mU LG Xp (U 0), t1Ph (LGQ.garden.sig 1) L γ δ k e σ u *
            (kernelProt L γ δ LGX (t2HX H) MX (fun _ => U 0) u (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LG₁ (t1HA c (t2HQ Xp H)) M₁ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LG₂ (t1HB (t2HQ Xp H)) M₂ (fun x => t1Clock 1 σ u (t1sw x.1.1)) 0
                    (fun _ => none) (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LG₃ (t1HC c (t2HQ Xp H)) M₃ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hM₁ 0)
  have hMb : ∀ K, ‖M K‖ ≤ CM * (CM * (CM * (CM * CM))) := by
    intro K
    rw [hMg K, hMQ, norm_mul, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact hMX _
    · exact hMc _ _
    · exact hM₁ _
    · exact hM₂ _
    · exact hM₃ _
  set HQ := t2HQ Xp H
  have hHQ := D.hH_Q L H hH
  set Φ := D.decEquiv h d
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hS : ∀ q, protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 1 σ) k (Φ.symm q) =
      (Mc (t1Star c L k q.2.1 0) (t1Star c L k q.2.1 1) * (t1Eps c q.2.1 : ℂ)) *
        ∫ u in t2mU LG Xp (U 0), t1Ph (LGQ.garden.sig 1) L γ δ k q.2.1 σ u *
          (protSummand L γ δ LGX (t2HX H) MX (fun _ => U 0) u (fun _ => none) k q.1 *
            (protSummand L γ δ LG₁ (t1HA c HQ) M₁ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                (k + latticePoint L q.2.1.1.1) q.2.2.1 *
              (protSummand L γ δ LG₂ (t1HB HQ) M₂ (fun x => t1Clock 1 σ u (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.1) q.2.2.2.1 *
                protSummand L γ δ LG₃ (t1HC c HQ) M₃ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.2) q.2.2.2.2))) := by
    intro q
    have := D.summand_t2m h hlA hlB hlC (Φ.symm q) L γ δ k H M MX MQ Mc M₁ M₂ M₃ hMg hMQ U s σ hσ
    rw [show D.decEquiv h d (Φ.symm q) = q from Φ.apply_symm_apply q] at this
    exact this
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun b => U b.1.1) s (trFix 1 σ) k
    (card_lone_le_of_plain D.plain) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 1 σ) k (Φ.symm q) :=
    (Φ.symm.summable_iff).mpr hsumG.of_norm
  rw [tsum_cut_assembly (t2mU LG Xp (U 0)) (volume_t2mU_ne_top LG Xp (U 0))
    (fun e => Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ))
    (fun e u => t1Ph (LGQ.garden.sig 1) L γ δ k e σ u)
    (fun e u => (norm_t1Ph _ L γ δ k e σ u).le) (fun e => stronglyMeasurable_t1Ph _ L γ δ k e σ)
    (fun p u => protSummand L γ δ LGX (t2HX H) MX (fun _ => U 0) u (fun _ => none) k p)
    (fun e i u => protSummand L γ δ LG₁ (t1HA c HQ) M₁ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
      (k + latticePoint L e.1.1) i)
    (fun e r u => protSummand L γ δ LG₂ (t1HB HQ) M₂ (fun x => t1Clock 1 σ u (t1sw x.1.1)) 0 (fun _ => none)
      (k + latticePoint L e.1.2.1) r)
    (fun e g u => protSummand L γ δ LG₃ (t1HC c HQ) M₃ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
      (k + latticePoint L e.1.2.2) g)
    (fun p => CM * leafMajorant L LGX (t2HX H) k p)
    (fun e i => CM * leafMajorant L LG₁ (t1HA c HQ) (k + latticePoint L e.1.1) i)
    (fun e r => CM * leafMajorant L LG₂ (t1HB HQ) (k + latticePoint L e.1.2.1) r)
    (fun e g => CM * leafMajorant L LG₃ (t1HC c HQ) (k + latticePoint L e.1.2.2) g)
    (fun p u => norm_protSummand_le L γ δ _ _ _ CM hMX _ _ _ _ p)
    (fun e i u => norm_protSummand_le L γ δ _ _ _ CM hM₁ _ _ _ _ i)
    (fun e r u => norm_protSummand_le L γ δ _ _ _ CM hM₂ _ _ _ _ r)
    (fun e g u => norm_protSummand_le L γ δ _ _ _ CM hM₃ _ _ _ _ g)
    ((summable_leafMajorant L LGX (t2HX H) k (fun _ => 0) 0
      (card_lone_le_of_decodesTree D.decX) (D.hH_X L H hH k)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₁ (t1HA c HQ) (k + latticePoint L e.1.1) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₁.1.1) (h.hH_A L HQ hHQ _)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₂ (t1HB HQ) (k + latticePoint L e.1.2.1) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₂.1.1) (h.hH_B L HQ hHQ _)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₃ (t1HC c HQ) (k + latticePoint L e.1.2.2) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₃.1.1) (h.hH_C L HQ hHQ _)).mul_left CM)
    (fun p => stronglyMeasurable_protSummand L γ δ LGX _ MX (fun _ _ => U 0) id _ _
      (fun _ => measurable_const) measurable_id p)
    (fun e i => stronglyMeasurable_protSummand L γ δ LG₁ _ M₁ (fun u x => t1Clock 1 σ u x.1.1) (fun _ => 0) _ _
      (fun x => measurable_t1Clock 1 σ x.1.1) measurable_const i)
    (fun e r => stronglyMeasurable_protSummand L γ δ LG₂ _ M₂ (fun u x => t1Clock 1 σ u (t1sw x.1.1)) (fun _ => 0)
      _ _ (fun x => measurable_t1Clock 1 σ (t1sw x.1.1)) measurable_const r)
    (fun e g => stronglyMeasurable_protSummand L γ δ LG₃ _ M₃ (fun u x => t1Clock 1 σ u x.1.1) (fun _ => 0) _ _
      (fun x => measurable_t1Clock 1 σ x.1.1) measurable_const g)
    _ hS hsum]
  simp only [kernelProt_eq_tsum]
  set cc := (coupling d L γ δ : ℂ)
  set C₀ := cc ^ LGX.garden.order * LGX.garden.zeta * (cc ^ LG₁.garden.order * LG₁.garden.zeta *
    (cc ^ LG₂.garden.order * LG₂.garden.zeta * (cc ^ LG₃.garden.order * LG₃.garden.zeta)))
  have hpull : ∀ e : T1E d,
      Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
        ∫ u in t2mU LG Xp (U 0), t1Ph (LGQ.garden.sig 1) L γ δ k e σ u *
          ((cc ^ LGX.garden.order * LGX.garden.zeta * ∑' p : GenDecoration LGX.garden d (fun _ => 0) 0,
              protSummand L γ δ LGX (t2HX H) MX (fun _ => U 0) u (fun _ => none) k p) *
            ((cc ^ LG₁.garden.order * LG₁.garden.zeta * ∑' i : GenDecoration LG₁.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₁ (t1HA c HQ) M₁ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.1) i) *
              ((cc ^ LG₂.garden.order * LG₂.garden.zeta * ∑' r : GenDecoration LG₂.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₂ (t1HB HQ) M₂ (fun x => t1Clock 1 σ u (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) r) *
                (cc ^ LG₃.garden.order * LG₃.garden.zeta * ∑' g : GenDecoration LG₃.garden d (fun _ => 0) 0,
                  protSummand L γ δ LG₃ (t1HC c HQ) M₃ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
          ∫ u in t2mU LG Xp (U 0), t1Ph (LGQ.garden.sig 1) L γ δ k e σ u *
            ((∑' p : GenDecoration LGX.garden d (fun _ => 0) 0,
                protSummand L γ δ LGX (t2HX H) MX (fun _ => U 0) u (fun _ => none) k p) *
              ((∑' i : GenDecoration LG₁.garden d (fun _ => 0) 0,
                  protSummand L γ δ LG₁ (t1HA c HQ) M₁ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.1) i) *
                ((∑' r : GenDecoration LG₂.garden d (fun _ => 0) 0,
                  protSummand L γ δ LG₂ (t1HB HQ) M₂ (fun x => t1Clock 1 σ u (t1sw x.1.1)) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) r) *
                  ∑' g : GenDecoration LG₃.garden d (fun _ => 0) 0,
                    protSummand L γ δ LG₃ (t1HC c HQ) M₃ (fun x => t1Clock 1 σ u x.1.1) 0 (fun _ => none)
                      (k + latticePoint L e.1.2.2) g)))) := by
    intro e
    have key : ∀ (A C : ℂ) (f g : ℝ → ℂ), (∀ u, f u = C * g u) →
        A * (∫ u in t2mU LG Xp (U 0), f u) = C * (A * ∫ u in t2mU LG Xp (U 0), g u) := by
      intro A C f g hfg
      simp_rw [hfg, integral_const_mul]
      ring
    exact key _ _ _ _ (fun u => by beta_reduce; ring)
  rw [tsum_congr hpull, tsum_mul_left, D.gd.order_glue, h.order_t1, D.gd.zeta_glue, h.zeta_t1', pow_add,
    pow_add, pow_add, pow_add]
  ring

end T2mData

end WaveTurbulence.Flower.ProtCut
