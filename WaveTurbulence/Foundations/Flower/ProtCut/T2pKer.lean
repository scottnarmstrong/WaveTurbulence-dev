/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T2p

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (c) on `kernelProt`, `ε = +` (the `+` chain empty, the root of tree `0` traced)

For a couple `LG` decoded by `type2 nil Xm (type1 c Q₁ Q₂ Q₃)` (as `SwGlueData LG nil Xm nil Qlp LGX LGB`: the chain `Xm`
of tree `1` as a paired tree `LGX` of sign `-1`, the lone-pair couple `LGB`; `T1Data` on `LGB`), upper clocks `U`, and
the root of tree `0` designated at `σ ≤ U 0` (`trFix 0 σ`):

    kernelProt LG H M (U ·) s (trFix 0 σ) k = c² Σ'_{y ∈ T1E} Mc(stars) ε_y ∫_{t2mU (swLG LG) Xm (U 1)} e^{πiB_y(σ−u)}
        K_X(U 1, port u)(k) · Q₁ Q₂ Q₃(σ_·(u))(k + y_·/L) du          (**`SwGlueData.kernelProt_t2p`**)

* `u` is the time of the partner `ρ' = (1, Xm.lonePath)` (the root of the tree `1` of `Q_lp`); the range is
  `{𝔏_{ρ'} < u < 𝔏_{ρ'} + 1, 0 < u, u < U 1}` (`layerAt (swLG LG) (0, Xm.lonePath) = layerAt LG (1, Xm.lonePath)`);
  `K_X` is the chain `X⁻` as a paired tree with lone-port time `u` (o104's `K_{X^{−ε}}(·, u)`);
* `B_y = ζ₀ δ L^{2γ} Ω_y` with `ζ₀ = LGB.garden.sig 0 = +1` (`t1Ph`); the sub-couples of `Q_lp` carry
  `t1Clock 0 σ u` (`σ` under `ρ`, `u` under `ρ'`), the profiles `H ∘ phiB` (the original labelling);
* multipliers: `swM M K = MX (K ∘ ι₁) · MB ((K ∘ ι₂) ∘ ndF)` (the glue of the relabelled couple; `MB` reads `Q_lp` in
  the original labelling) and `T1Data.MultFactors MB Mc M₁ M₂ M₃`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

theorem lfF_input {G : Garden 2} (ℓ : GLeaf G.tree) (hℓ : ℓ ∈ inputLeaves G) : lfF ℓ ∈ inputLeaves (swGarden G) := by
  rw [mem_inputLeaves] at hℓ ⊢
  have e1 : (swGarden G).sign (lfF ℓ).toNode = G.sign (lfB (lfF ℓ)).toNode := rfl
  have e2 : (swGarden G).mark (lfF ℓ) = G.mark (lfB (lfF ℓ)) := rfl
  rw [e1, e2, lfB_lfF]
  exact hℓ

namespace SwGlueData

variable {LG : LayeredGarden 2} {Xm : RegChain} {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LGX : LayeredGarden 1}
  {LGB : LayeredGarden 2} (D : SwGlueData LG .nil Xm .nil (.type1 c Q₁ Q₂ Q₃) LGX LGB)
  {LG₁ LG₂ LG₃ : LayeredGarden 2} (h : T1Data c Q₁ Q₂ Q₃ LGB.garden LG₁.garden LG₂.garden LG₃.garden)
include D h

/-- The relabelled couple as a `T2mData`. -/
theorem T : T2mData (swLG LG) Xm LGX (swLG LGB) := D.toT2m (h.root_mem 1)

/-- **Decorations**: chain × (exceptional data × three sub-couples of `Q_lp`), through the relabelling. -/
def decEquivP (d : ℕ) : GenDecoration LG.garden d (fun _ => 0) 0 ≃
    GenDecoration LGX.garden d (fun _ => 0) 0 × (T1E d × (GenDecoration LG₁.garden d (fun _ => 0) 0 ×
      (GenDecoration LG₂.garden d (fun _ => 0) 0 × GenDecoration LG₃.garden d (fun _ => 0) 0))) :=
  ((swDec d D.dec.1.1).trans ((D.T h).gdEquiv d)).trans
    (Equiv.prodCongr (Equiv.refl _) ((swDec d D.decB.1.1).symm.trans (h.decEquiv d)))

theorem decEquivP_apply {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0) :
    D.decEquivP h d κ = (((D.T h).gdEquiv d (swDec d D.dec.1.1 κ)).1,
      h.decEquiv d ((swDec d D.decB.1.1).symm ((D.T h).gdEquiv d (swDec d D.dec.1.1 κ)).2)) := rfl

theorem hH_B {d : ℕ} (L : ℝ) (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|) :
    ∀ ℓ ∈ inputLeaves LGB.garden, ∀ k' : Mom d,
      Summable fun n : Fin d → ℤ => |H (phiB Xm.lonePath ℓ.1) (k' + latticePoint L n)| := by
  intro ℓ hℓ k'
  have h1 := (D.T h).hH_Q L (swH H) (hH_sw L H hH) (lfF ℓ) (lfF_input ℓ hℓ) k'
  have e : t2HQ Xm (swH H) (lfF ℓ).1 = H (phiB Xm.lonePath ℓ.1) := congrFun (D.t2HQ_sw H) ℓ.1
  rw [e] at h1
  exact h1

theorem summand_sw0 {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0) (L γ δ : ℝ) (k : Mom d)
    (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ) (U : Fin 2 → ℝ) (s σ : ℝ) :
    protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k κ =
      protSummand L γ δ (swLG LG) (swH H) (swM M) (fun b => swU U b.1.1) s (trFix 1 σ) k
        (swDec d D.dec.1.1 κ) := by
  have hfix : (fun b => trFix 0 σ (brB b) : GBranch (swLG LG).garden.tree → Option ℝ) = trFix 1 σ :=
    funext fun b => trFix_brB0 σ b
  have := (protSummand_sw D.dec.1.1 L γ δ H M (fun b => U b.1.1) s (trFix 0 σ) k κ).symm
  rw [hfix] at this
  exact this

/-- **o104 Prop 7.4 (c) at one decoration, `ε = +`.** -/
theorem summand_t2p (hlA : ∀ z, LG₁.layer z = LGB.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LGB.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LGB.layer (h.ιC z)) {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0)
    (L γ δ : ℝ) (k : Mom d) (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (MX : (GNode LGX.garden.tree → Mom d) → ℂ) (MB : (GNode LGB.garden.tree → Mom d) → ℂ)
    (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ)
    (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ) (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ)
    (hMg : ∀ K, swM M K = MX (K ∘ D.gd.ι₁) * MB ((K ∘ D.gd.ι₂) ∘ ndF))
    (hMB : h.MultFactors MB Mc M₁ M₂ M₃) (U : Fin 2 → ℝ) (s σ : ℝ) (hσ : σ ≤ U 0) :
    protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k κ =
      (Mc (t1Star c L k (D.decEquivP h d κ).2.1 0) (t1Star c L k (D.decEquivP h d κ).2.1 1) *
          (t1Eps c (D.decEquivP h d κ).2.1 : ℂ)) *
        ∫ u in t2mU (swLG LG) Xm (U 1), t1Ph (LGB.garden.sig 0) L γ δ k (D.decEquivP h d κ).2.1 σ u *
          (protSummand L γ δ LGX (t2HX (swH H)) MX (fun _ => U 1) u (fun _ => none) k (D.decEquivP h d κ).1 *
            (protSummand L γ δ LG₁ (t1HA c (fun a => H (phiB Xm.lonePath a))) M₁ (fun x => t1Clock 0 σ u x.1.1) 0
                (fun _ => none) (k + latticePoint L (D.decEquivP h d κ).2.1.1.1) (D.decEquivP h d κ).2.2.1 *
              (protSummand L γ δ LG₂ (t1HB (fun a => H (phiB Xm.lonePath a))) M₂
                  (fun x => t1Clock 0 σ u (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L (D.decEquivP h d κ).2.1.1.2.1) (D.decEquivP h d κ).2.2.2.1 *
                protSummand L γ δ LG₃ (t1HC c (fun a => H (phiB Xm.lonePath a))) M₃
                  (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L (D.decEquivP h d κ).2.1.1.2.2) (D.decEquivP h d κ).2.2.2.2))) := by
  rw [D.summand_sw0 h κ L γ δ k H M U s σ, (D.T h).summand_t2mGlue (swDec d D.dec.1.1 κ) L γ δ k (swH H) (swM M)
    MX (fun K' => MB (K' ∘ ndF)) hMg (swU U) s σ, D.decEquivP_apply h κ]
  simp only [swU_zero]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_t2mU _ Xm _) fun u hu => ?_
  rw [protSummand_sw_back D.decB.1.1 L γ δ _ _ _ s _ k]
  have e2 : (fun b : GBranch LGB.garden.tree => swU U (brF b).1.1) = fun b => U b.1.1 :=
    funext fun b => by simp only [swU, brF, t1sw_t1sw]
  have e3 : (fun b : GBranch LGB.garden.tree => rootsFix (t1Clock 1 σ u) (brF b)) = rootsFix (t1Clock 0 σ u) :=
    funext fun b => rootsFix_brF σ u b
  have e4 : (fun K : GNode LGB.garden.tree → Mom d => MB ((K ∘ ndB) ∘ ndF)) = MB := by
    funext K
    congr 1
    funext x
    exact congrArg K (ndB_ndF x)
  rw [D.t2HQ_sw H, e2, e3, e4, h.summand_t1Both _ L k hlA hlB hlC γ δ _ _ Mc M₁ M₂ M₃ hMB U s 0 σ u hσ
    (show u ≤ U (t1sw 0) from hu.2.2.2.le)]
  ring

/-- **o104 Prop 7.4 (c) on `kernelProt`, `ε = +`.** -/
theorem kernelProt_t2p (hlA : ∀ z, LG₁.layer z = LGB.layer (h.ιA z))
    (hlB : ∀ z, LG₂.layer z = LGB.layer (h.ιB z)) (hlC : ∀ z, LG₃.layer z = LGB.layer (h.ιC z))
    (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (MX : (GNode LGX.garden.tree → Mom d) → ℂ)
    (MB : (GNode LGB.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ) (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ)
    (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ)
    (hMg : ∀ K, swM M K = MX (K ∘ D.gd.ι₁) * MB ((K ∘ D.gd.ι₂) ∘ ndF)) (hMB : h.MultFactors MB Mc M₁ M₂ M₃)
    (CM : ℝ) (hMX : ∀ K, ‖MX K‖ ≤ CM) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hM₁ : ∀ K, ‖M₁ K‖ ≤ CM)
    (hM₂ : ∀ K, ‖M₂ K‖ ≤ CM) (hM₃ : ∀ K, ‖M₃ K‖ ≤ CM) (U : Fin 2 → ℝ) (s σ : ℝ) (hσ : σ ≤ U 0) (k : Mom d) :
    kernelProt L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 *
        ∑' e : T1E d, Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
          ∫ u in t2mU (swLG LG) Xm (U 1), t1Ph (LGB.garden.sig 0) L γ δ k e σ u *
            (kernelProt L γ δ LGX (t2HX (swH H)) MX (fun _ => U 1) u (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LG₁ (t1HA c (fun a => H (phiB Xm.lonePath a))) M₁ (fun x => t1Clock 0 σ u x.1.1) 0
                  (fun _ => none) (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LG₂ (t1HB (fun a => H (phiB Xm.lonePath a))) M₂
                    (fun x => t1Clock 0 σ u (t1sw x.1.1)) 0 (fun _ => none) (k + latticePoint L e.1.2.1)
                    (fun _ => 0) 0 *
                  kernelProt L γ δ LG₃ (t1HC c (fun a => H (phiB Xm.lonePath a))) M₃
                    (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none) (k + latticePoint L e.1.2.2)
                    (fun _ => 0) 0))) := by
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hM₁ 0)
  have hMb : ∀ K, ‖M K‖ ≤ CM * (CM * (CM * (CM * CM))) := by
    intro K
    have e : M K = swM M (K ∘ ndB) := by
      show M K = M ((K ∘ ndB) ∘ ndF)
      congr 1
      funext x
      exact congrArg K (ndB_ndF x).symm
    rw [e, hMg, hMB, norm_mul, norm_mul, norm_mul, norm_mul]
    gcongr
    · exact hMX _
    · exact hMc _ _
    · exact hM₁ _
    · exact hM₂ _
    · exact hM₃ _
  set HB : LeafProfiles 2 d := fun a => H (phiB Xm.lonePath a)
  have hHB : ∀ ℓ ∈ inputLeaves LGB.garden, ∀ k' : Mom d,
      Summable fun n : Fin d → ℤ => |HB ℓ.1 (k' + latticePoint L n)| := D.hH_B h L H hH
  set Φ := D.decEquivP h d
  rw [kernelProt_eq_tsum, ← Φ.symm.tsum_eq]
  have hS : ∀ q, protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k (Φ.symm q) =
      (Mc (t1Star c L k q.2.1 0) (t1Star c L k q.2.1 1) * (t1Eps c q.2.1 : ℂ)) *
        ∫ u in t2mU (swLG LG) Xm (U 1), t1Ph (LGB.garden.sig 0) L γ δ k q.2.1 σ u *
          (protSummand L γ δ LGX (t2HX (swH H)) MX (fun _ => U 1) u (fun _ => none) k q.1 *
            (protSummand L γ δ LG₁ (t1HA c HB) M₁ (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none)
                (k + latticePoint L q.2.1.1.1) q.2.2.1 *
              (protSummand L γ δ LG₂ (t1HB HB) M₂ (fun x => t1Clock 0 σ u (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.1) q.2.2.2.1 *
                protSummand L γ δ LG₃ (t1HC c HB) M₃ (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L q.2.1.1.2.2) q.2.2.2.2))) := by
    intro q
    have := D.summand_t2p h hlA hlB hlC (Φ.symm q) L γ δ k H M MX MB Mc M₁ M₂ M₃ hMg hMB U s σ hσ
    rw [show D.decEquivP h d (Φ.symm q) = q from Φ.apply_symm_apply q] at this
    exact this
  have hsumG := summable_protSummand_norm L γ δ LG H M _ hMb (fun b => U b.1.1) s (trFix 0 σ) k
    (card_lone_le_of_plain D.dec.1.1) (fun ℓ hℓ => hH ℓ hℓ k)
  have hsum : Summable fun q => protSummand L γ δ LG H M (fun b => U b.1.1) s (trFix 0 σ) k (Φ.symm q) :=
    (Φ.symm.summable_iff).mpr hsumG.of_norm
  rw [tsum_cut_assembly (t2mU (swLG LG) Xm (U 1)) (volume_t2mU_ne_top _ Xm _)
    (fun e => Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ))
    (fun e u => t1Ph (LGB.garden.sig 0) L γ δ k e σ u)
    (fun e u => (norm_t1Ph _ L γ δ k e σ u).le) (fun e => stronglyMeasurable_t1Ph _ L γ δ k e σ)
    (fun p u => protSummand L γ δ LGX (t2HX (swH H)) MX (fun _ => U 1) u (fun _ => none) k p)
    (fun e i u => protSummand L γ δ LG₁ (t1HA c HB) M₁ (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none)
      (k + latticePoint L e.1.1) i)
    (fun e r u => protSummand L γ δ LG₂ (t1HB HB) M₂ (fun x => t1Clock 0 σ u (t1sw x.1.1)) 0 (fun _ => none)
      (k + latticePoint L e.1.2.1) r)
    (fun e g u => protSummand L γ δ LG₃ (t1HC c HB) M₃ (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none)
      (k + latticePoint L e.1.2.2) g)
    (fun p => CM * leafMajorant L LGX (t2HX (swH H)) k p)
    (fun e i => CM * leafMajorant L LG₁ (t1HA c HB) (k + latticePoint L e.1.1) i)
    (fun e r => CM * leafMajorant L LG₂ (t1HB HB) (k + latticePoint L e.1.2.1) r)
    (fun e g => CM * leafMajorant L LG₃ (t1HC c HB) (k + latticePoint L e.1.2.2) g)
    (fun p u => norm_protSummand_le L γ δ _ _ _ CM hMX _ _ _ _ p)
    (fun e i u => norm_protSummand_le L γ δ _ _ _ CM hM₁ _ _ _ _ i)
    (fun e r u => norm_protSummand_le L γ δ _ _ _ CM hM₂ _ _ _ _ r)
    (fun e g u => norm_protSummand_le L γ δ _ _ _ CM hM₃ _ _ _ _ g)
    ((summable_leafMajorant L LGX (t2HX (swH H)) k (fun _ => 0) 0
      (card_lone_le_of_decodesTree D.decX) ((D.T h).hH_X L (swH H) (hH_sw L H hH) k)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₁ (t1HA c HB) (k + latticePoint L e.1.1) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₁.1.1) (h.hH_A L HB hHB _)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₂ (t1HB HB) (k + latticePoint L e.1.2.1) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₂.1.1) (h.hH_B L HB hHB _)).mul_left CM)
    (fun e => (summable_leafMajorant L LG₃ (t1HC c HB) (k + latticePoint L e.1.2.2) (fun _ => 0) 0
      (card_lone_le_of_plain h.dec₃.1.1) (h.hH_C L HB hHB _)).mul_left CM)
    (fun p => stronglyMeasurable_protSummand L γ δ LGX _ MX (fun _ _ => U 1) id _ _
      (fun _ => measurable_const) measurable_id p)
    (fun e i => stronglyMeasurable_protSummand L γ δ LG₁ _ M₁ (fun u x => t1Clock 0 σ u x.1.1) (fun _ => 0) _ _
      (fun x => measurable_t1Clock 0 σ x.1.1) measurable_const i)
    (fun e r => stronglyMeasurable_protSummand L γ δ LG₂ _ M₂ (fun u x => t1Clock 0 σ u (t1sw x.1.1)) (fun _ => 0)
      _ _ (fun x => measurable_t1Clock 0 σ (t1sw x.1.1)) measurable_const r)
    (fun e g => stronglyMeasurable_protSummand L γ δ LG₃ _ M₃ (fun u x => t1Clock 0 σ u x.1.1) (fun _ => 0) _ _
      (fun x => measurable_t1Clock 0 σ x.1.1) measurable_const g)
    _ hS hsum]
  simp only [kernelProt_eq_tsum]
  set cc := (coupling d L γ δ : ℂ)
  set C₀ := cc ^ LGX.garden.order * LGX.garden.zeta * (cc ^ LG₁.garden.order * LG₁.garden.zeta *
    (cc ^ LG₂.garden.order * LG₂.garden.zeta * (cc ^ LG₃.garden.order * LG₃.garden.zeta)))
  have hpull : ∀ e : T1E d,
      Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
        ∫ u in t2mU (swLG LG) Xm (U 1), t1Ph (LGB.garden.sig 0) L γ δ k e σ u *
          ((cc ^ LGX.garden.order * LGX.garden.zeta * ∑' p : GenDecoration LGX.garden d (fun _ => 0) 0,
              protSummand L γ δ LGX (t2HX (swH H)) MX (fun _ => U 1) u (fun _ => none) k p) *
            ((cc ^ LG₁.garden.order * LG₁.garden.zeta * ∑' i : GenDecoration LG₁.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₁ (t1HA c HB) M₁ (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.1) i) *
              ((cc ^ LG₂.garden.order * LG₂.garden.zeta * ∑' r : GenDecoration LG₂.garden d (fun _ => 0) 0,
                protSummand L γ δ LG₂ (t1HB HB) M₂ (fun x => t1Clock 0 σ u (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) r) *
                (cc ^ LG₃.garden.order * LG₃.garden.zeta * ∑' g : GenDecoration LG₃.garden d (fun _ => 0) 0,
                  protSummand L γ δ LG₃ (t1HC c HB) M₃ (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) g)))) =
        C₀ * (Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
          ∫ u in t2mU (swLG LG) Xm (U 1), t1Ph (LGB.garden.sig 0) L γ δ k e σ u *
            ((∑' p : GenDecoration LGX.garden d (fun _ => 0) 0,
                protSummand L γ δ LGX (t2HX (swH H)) MX (fun _ => U 1) u (fun _ => none) k p) *
              ((∑' i : GenDecoration LG₁.garden d (fun _ => 0) 0,
                  protSummand L γ δ LG₁ (t1HA c HB) M₁ (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.1) i) *
                ((∑' r : GenDecoration LG₂.garden d (fun _ => 0) 0,
                  protSummand L γ δ LG₂ (t1HB HB) M₂ (fun x => t1Clock 0 σ u (t1sw x.1.1)) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) r) *
                  ∑' g : GenDecoration LG₃.garden d (fun _ => 0) 0,
                    protSummand L γ δ LG₃ (t1HC c HB) M₃ (fun x => t1Clock 0 σ u x.1.1) 0 (fun _ => none)
                      (k + latticePoint L e.1.2.2) g)))) := by
    intro e
    have key : ∀ (A C : ℂ) (f g : ℝ → ℂ), (∀ u, f u = C * g u) →
        A * (∫ u in t2mU (swLG LG) Xm (U 1), f u) = C * (A * ∫ u in t2mU (swLG LG) Xm (U 1), g u) := by
      intro A C f g hfg
      simp_rw [hfg, integral_const_mul]
      ring
    exact key _ _ _ _ (fun u => by beta_reduce; ring)
  have ho : LG.garden.order = LGX.garden.order + (LG₁.garden.order + LG₂.garden.order + LG₃.garden.order + 2) := by
    have e1 : (swLG LG).garden.order = LG.garden.order := order_sw
    have e2 : (swLG LGB).garden.order = LGB.garden.order := order_sw
    rw [← e1, (D.T h).gd.order_glue, e2, h.order_t1]
  have hz : LG.garden.zeta = LGX.garden.zeta * (LG₁.garden.zeta * (LG₂.garden.zeta * LG₃.garden.zeta)) := by
    have e1 : (swLG LG).garden.zeta = LG.garden.zeta := zeta_sw
    have e2 : (swLG LGB).garden.zeta = LGB.garden.zeta := zeta_sw
    rw [← e1, (D.T h).gd.zeta_glue, e2, h.zeta_t1']
  rw [tsum_congr hpull, tsum_mul_left, ho, hz, pow_add, pow_add, pow_add, pow_add]
  ring

omit D h in
theorem bstar_brF {d : ℕ} {T : Fin 2 → TTree} (K : GNode (swT T) → Mom d) (y : GBranch T) :
    bstar K (brF y) = bstar (K ∘ ndF) y := by
  funext i
  refine Fin.cases rfl (fun j => rfl) i

/-- **A branch-local multiplier satisfies the multiplier hypotheses of `kernelProt_t2p`.** -/
theorem multFactors_local_t2p {d : ℕ} (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) :
    (∀ K, swM (fun K => ∏ b, f b (bstar K b)) K =
        (fun K' => ∏ x, f (brB (D.gd.ofSum (.inl x))) (bstar K' x)) (K ∘ D.gd.ι₁) *
          (fun K' => ∏ y, f (brB (D.gd.ofSum (.inr (brF y)))) (bstar K' y)) ((K ∘ D.gd.ι₂) ∘ ndF)) ∧
      h.MultFactors (fun K' => ∏ y, f (brB (D.gd.ofSum (.inr (brF y)))) (bstar K' y))
        (fun A B => f (brB (D.gd.ofSum (.inr (brF (h.rt 0))))) A * f (brB (D.gd.ofSum (.inr (brF (h.rt 1))))) B)
        (fun K => ∏ x, f (brB (D.gd.ofSum (.inr (brF (h.βA x))))) (bstar K x))
        (fun K => ∏ x, f (brB (D.gd.ofSum (.inr (brF (h.βB x))))) (bstar K x))
        (fun K => ∏ x, f (brB (D.gd.ofSum (.inr (brF (h.βC x))))) (bstar K x)) := by
  refine ⟨fun K => ?_, h.multFactors_local (fun y => f (brB (D.gd.ofSum (.inr (brF y)))))⟩
  rw [swM_local]
  beta_reduce
  rw [D.gd.prod_branch]
  have hl : ∀ x, bstar K (D.gd.ofSum (.inl x)) = bstar (K ∘ D.gd.ι₁) x := by
    intro x; funext i
    refine Fin.cases rfl (fun j => ?_) i
    show K ((D.gd.ofSum (.inl x)).child j) = K (D.gd.ι₁ (x.child j))
    rw [D.gd.ofSum_inl_child]
  have hr : ∀ y, bstar K (D.gd.ofSum (.inr y)) = bstar (K ∘ D.gd.ι₂) y := by
    intro y; funext i
    refine Fin.cases rfl (fun j => ?_) i
    show K ((D.gd.ofSum (.inr y)).child j) = K (D.gd.ι₂ (y.child j))
    rw [D.gd.ofSum_inr_child]
  simp only [hl, hr]
  congr 1
  refine (Fintype.prod_equiv brEquiv _ _ (fun y => ?_))
  show f (brB (D.gd.ofSum (.inr y))) (bstar (K ∘ D.gd.ι₂) y) =
    f (brB (D.gd.ofSum (.inr (brF (brB y))))) (bstar ((K ∘ D.gd.ι₂) ∘ ndF) (brB y))
  rw [brF_brB, ← bstar_brF, brF_brB]

end SwGlueData

end WaveTurbulence.Flower.ProtCut
