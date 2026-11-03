/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CouplingS

/-!
# DH21 Lemma 5.4, `J R`: set-up and the bounds of the fixed functions

For `𝒥^{(1)} = ∫ m^{(1)} J_{ℓ₁;γ₁,γ₂}` and `ℛ^{(2)} = ∫ m^{(2)} R_{ℓ₂+εα₁, ℓ₃+εα₁; γ₃,γ₄,γ₅}`,
the composition kernel is (DH21 L1009–L1011)
`χ_∞(x₁)/x₁ · J_{ℓ₁;γ₁,γ₂} J_{ℓ₃+εα₁;γ₃,γ₄}` with `x₁ = ℓ₂ + εα₁ + γ₅`, and the `J J` split gives
three pieces with `x₀ = ℓ₃ - ℓ₁ + εα₁ + γ₂ + γ₃`:

* `χ₀` piece: `kerM(x₀) χ_∞(x₁)/x₁`, bundle `ℓ₁`, `γ' = (γ₁ + σ, γ₂ + γ₃ + γ₄ - σ)`;
* `χ_∞` pieces: `±Φ(x₀) χ_∞(x₁)/x₁`, bundles `ℓ₃ + εα₁` and `ℓ₁`.

The variables are `α ∈ (ι₁ ⊕ ι₂) ⊕ Unit → ℝ` (the special variable is `α (inr ())`); the natural
labelling `ι₁ ⊕ Option ι₂` is recovered with `ClassJ.reindex`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section Equiv

variable (Q : Type*) [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- `((γ₁,γ₂),((γ₃,(γ₄,γ₅)),q)) ↦ ((γ₁,γ₄),((γ₂,γ₃),(γ₅,q)))`. -/
@[expose] def eJR : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Q) ≃ᵐ (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × Q)) where
  toFun z := ((z.1.1, z.2.1.2.1), ((z.1.2, z.2.1.1), (z.2.1.2.2, z.2.2)))
  invFun z := ((z.1.1, z.2.1.1), ((z.2.1.2, (z.1.2, z.2.2.1)), z.2.2.2))
  left_inv z := rfl
  right_inv z := rfl
  measurable_toFun := by
    change Measurable fun z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Q) =>
      ((z.1.1, z.2.1.2.1), ((z.1.2, z.2.1.1), (z.2.1.2.2, z.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × Q)) =>
      ((z.1.1, z.2.1.1), ((z.2.1.2, (z.1.2, z.2.2.1)), z.2.2.2))
    fun_prop

omit [SFinite (volume : Measure Q)] in
@[simp] theorem eJR_apply (z : (ℝ × ℝ) × ((ℝ × (ℝ × ℝ)) × Q)) :
    eJR Q z = ((z.1.1, z.2.1.2.1), ((z.1.2, z.2.1.1), (z.2.1.2.2, z.2.2))) := rfl

theorem measurePreserving_eJR : MeasurePreserving (eJR Q) := by
  have r1 := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ × ℝ) (γ₁ := Q))
  have r2 : MeasurePreserving (Prod.map (id : ℝ → ℝ)
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := Q))) :=
    MeasurePreserving.prod (MeasurePreserving.id volume) volume_preserving_prodAssoc
  have r3 := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ × Q)).symm
  have hre := r3.comp (r2.comp r1)
  have hre' : MeasurePreserving (Prod.map (id : ℝ × ℝ → ℝ × ℝ)
      ((MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ × Q)).symm ∘
        Prod.map (id : ℝ → ℝ) (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := Q)) ∘
          (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ × ℝ) (γ := Q)))) :=
    MeasurePreserving.prod (MeasurePreserving.id volume) hre
  have := (measurePreserving_eJJ (ℝ × Q)).comp hre'
  convert this using 1
  funext z
  rfl

end Equiv

section Bundles

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- A bundle on `(ι₁ ⊕ ι₂) ⊕ Unit` from its three blocks. -/
@[expose] def y3 (f : ι₁ → ℤ) (g : ι₂ → ℤ) (e : ℤ) : (ι₁ ⊕ ι₂) ⊕ Unit → ℤ :=
  Sum.elim (Sum.elim f g) fun _ => e

theorem isBundle_y3 {f : ι₁ → ℤ} {g : ι₂ → ℤ} {e : ℤ} (hf : IsBundle f) (hg : IsBundle g)
    (he : |e| ≤ 1) : IsBundle (y3 f g e) := by
  rintro ((i | i) | u)
  · exact hf i
  · exact hg i
  · exact he

theorem bundle_y3 (f : ι₁ → ℤ) (g : ι₂ → ℤ) (e : ℤ) (α : (ι₁ ⊕ ι₂) ⊕ Unit → ℝ) :
    bundle (y3 f g e) α = bundle f (vA α) + bundle g (vB α) + e * α (Sum.inr ()) := by
  simp [bundle, y3, Fintype.sum_sum_type, vA, vB]

theorem abs_sign_le {e : ℤ} (he : e = 1 ∨ e = -1) : |e| ≤ 1 := by
  rcases he with rfl | rfl <;> simp

theorem isBundle_neg {ι : Type*} {f : ι → ℤ} (hf : IsBundle f) : IsBundle fun i => -f i :=
  fun i => by simpa using hf i

theorem isBundle_zero {ι : Type*} : IsBundle (0 : ι → ℤ) := fun i => by simp

end Bundles

section Gamma

/-- `‖∂^c (χ_∞(x)/x)‖ ≤ C_Φ A^c (2c)! (1 + |x|)^{-1}`, as extended reals. -/
theorem enorm_iteratedDeriv_chiInvRc_le (c : ℕ) (x : ℝ) :
    ‖iteratedDeriv c (fun y => (chiInvR y : ℂ)) x‖ₑ ≤
      gev CPhi Achi c * ENNReal.ofReal ((1 + |x|)⁻¹) := by
  rw [← ofReal_norm, norm_iteratedDeriv_ofReal contDiff_chiInvR, gev,
    ← ENNReal.ofReal_mul (by have := Achi_nonneg; have := CPhi_nonneg; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact chiInvR_gevrey c x

theorem enorm_iteratedDeriv_phiR_le' (c : ℕ) (x : ℝ) :
    ‖iteratedDeriv c phiR x‖ₑ ≤ gev CPhi Achi c * ENNReal.ofReal ((1 + |x|)⁻¹) := by
  rw [← ofReal_norm, gev,
    ← ENNReal.ofReal_mul (by have := Achi_nonneg; have := CPhi_nonneg; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact phiR_gevrey c x

theorem contDiff_chiInvRc : ContDiff ℝ ∞ fun y => (chiInvR y : ℂ) :=
  Complex.ofRealCLM.contDiff.comp contDiff_chiInvR

/-- Single-form substitution in the special variable. -/
theorem lintegral_affine_one {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (X : ℝ) {f : ℝ → ℝ≥0∞} :
    ∫⁻ s, f (X + ε * s) = ∫⁻ u, f u := by
  have := lintegral_affine_pair (F := fun u _ => f u) hε X 0
  simpa using this

theorem lintegral_unitFun {G : ℝ → ℝ≥0∞} : ∫⁻ s : Unit → ℝ, G (s ()) = ∫⁻ t, G t :=
  (volume_preserving_funUnique Unit ℝ).lintegral_comp_emb
    (MeasurableEquiv.funUnique Unit ℝ).measurableEmbedding G

/-- The coupling `kerM(x₀) χ_∞(x₁)/x₁` of the `χ₀` piece of `J R`. -/
@[expose] noncomputable def KMR (x : Fin 2 → ℝ) (q : ℝ × ℝ) : ℂ :=
  kerM (x 0) q * (chiInvR (x 1) : ℂ)

/-- The coupling `Φ(x₀) χ_∞(x₁)/x₁` of the `χ_∞` pieces of `J R`. -/
@[expose] noncomputable def KPR (x : Fin 2 → ℝ) (_ : Unit) : ℂ := phiR (x 0) * (chiInvR (x 1) : ℂ)

/-- The coupling `-Φ(x₀) χ_∞(x₁)/x₁`. -/
@[expose] noncomputable def KPRn (x : Fin 2 → ℝ) (_ : Unit) : ℂ :=
  -(phiR (x 0) * (chiInvR (x 1) : ℂ))

theorem KMR_eq (q : ℝ × ℝ) :
    (fun x => KMR x q) = prod2 (fun y => kerM y q) fun y => (chiInvR y : ℂ) := rfl

theorem KPR_eq (q : Unit) : (fun x => KPR x q) = prod2 phiR fun y => (chiInvR y : ℂ) := rfl

theorem KPRn_eq (q : Unit) :
    (fun x => KPRn x q) = fun x => -prod2 phiR (fun y => (chiInvR y : ℂ)) x := rfl

/-- The pointwise bound of the `χ₀` coupling of `J R`. -/
theorem enorm_iteratedFDeriv_KMR_le (c : ℕ) (x : Fin 2 → ℝ) (q : ℝ × ℝ) :
    ((1 + ‖x 1‖ₑ) + (1 + ‖q.1‖ₑ)) * ‖iteratedFDeriv ℝ c (fun x => KMR x q) x‖ₑ ≤
      ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
        ((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (x 0) *
          (2 * ((1 + ‖q.1‖ₑ) * gM j q)) * gev CPhi Achi (c - j)) := by
  rw [KMR_eq]
  refine (mul_le_mul' le_rfl (enorm_iteratedFDeriv_prod2_le (contDiff_kerM q)
    contDiff_chiInvRc c x)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := enorm_iteratedDeriv_kerM_le_ind j (x 0) q
  have h2 := enorm_iteratedDeriv_chiInvRc_le (c - j) (x 1)
  have hx1 : (1 + ‖x 1‖ₑ) * ENNReal.ofReal ((1 + |x 1|)⁻¹) = 1 := by
    rw [show (1 : ℝ≥0∞) + ‖x 1‖ₑ = ENNReal.ofReal (1 + |x 1|) by
      rw [ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one, ← Real.norm_eq_abs,
        ofReal_norm], ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
      ENNReal.ofReal_one]
  have hq1 : ENNReal.ofReal ((1 + |x 1|)⁻¹) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (inv_le_one_of_one_le₀ (by linarith [abs_nonneg (x 1)]))
  calc ((1 + ‖x 1‖ₑ) + (1 + ‖q.1‖ₑ)) * ((c.choose j : ℝ≥0∞) *
        ‖iteratedDeriv j (fun y => kerM y q) (x 0)‖ₑ *
          ‖iteratedDeriv (c - j) (fun y => (chiInvR y : ℂ)) (x 1)‖ₑ)
      ≤ ((1 + ‖x 1‖ₑ) + (1 + ‖q.1‖ₑ)) * ((c.choose j : ℝ≥0∞) *
          ((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (x 0) * gM j q) *
          (gev CPhi Achi (c - j) * ENNReal.ofReal ((1 + |x 1|)⁻¹))) := by gcongr
    _ = (c.choose j : ℝ≥0∞) * ((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (x 0) *
          (((1 + ‖x 1‖ₑ) * ENNReal.ofReal ((1 + |x 1|)⁻¹) +
            (1 + ‖q.1‖ₑ) * ENNReal.ofReal ((1 + |x 1|)⁻¹)) * gM j q) *
          gev CPhi Achi (c - j)) := by ring
    _ ≤ (c.choose j : ℝ≥0∞) * ((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (x 0) *
          (2 * ((1 + ‖q.1‖ₑ) * gM j q)) * gev CPhi Achi (c - j)) := by
        have key : (1 + (1 + ‖q.1‖ₑ) * ENNReal.ofReal ((1 + |x 1|)⁻¹)) * gM j q ≤
            2 * ((1 + ‖q.1‖ₑ) * gM j q) :=
          calc (1 + (1 + ‖q.1‖ₑ) * ENNReal.ofReal ((1 + |x 1|)⁻¹)) * gM j q
              ≤ ((1 + ‖q.1‖ₑ) + (1 + ‖q.1‖ₑ) * 1) * gM j q :=
                mul_le_mul' (add_le_add le_self_add (mul_le_mul' le_rfl hq1)) le_rfl
            _ = 2 * ((1 + ‖q.1‖ₑ) * gM j q) := by ring
        rw [hx1]
        exact mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl key) le_rfl)

/-- **`Γ` for the `χ₀` piece of `J R`** (DH21 (uniformbound0), L1012). -/
theorem gamma_KMR_le {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (X₀ X₁ : ℝ)
    (v : (Unit → ℝ) → ℝ × ℝ → Fin 2 → ℝ) (hv0 : ∀ s q, v s q 0 = X₀ + ε * s ())
    (hv1 : ∀ s q, v s q 1 = X₁ + ε * s ()) (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q : ℝ × ℝ, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 1‖ₑ) + (1 + ‖q.1‖ₑ)) *
      ‖iteratedFDeriv ℝ c (fun x => KMR x q) (v s q)‖ₑ ≤ gev (16 * (CkM * IM) * CPhi) A c := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hε' : (ε : ℝ) = 1 ∨ (ε : ℝ) = -1 := by rcases hε with rfl | rfl <;> simp
  have hind : ∫⁻ s : Unit → ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))
      (X₀ + ε * s ()) = 2 := by
    rw [lintegral_unitFun (G := fun t => (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞))
      (X₀ + ε * t)), lintegral_affine_one hε' X₀, lintegral_indicator measurableSet_Icc,
      setLIntegral_const, Real.volume_Icc, one_mul]
    norm_num
  calc ∫⁻ q : ℝ × ℝ, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 1‖ₑ) + (1 + ‖q.1‖ₑ)) *
        ‖iteratedFDeriv ℝ c (fun x => KMR x q) (v s q)‖ₑ
      ≤ ∫⁻ q : ℝ × ℝ, ∫⁻ s : Unit → ℝ, ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
          ((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (X₀ + ε * s ()) *
            (2 * ((1 + ‖q.1‖ₑ) * gM j q)) * gev CPhi Achi (c - j)) := by
        refine lintegral_mono fun q => lintegral_mono fun s => ?_
        have := enorm_iteratedFDeriv_KMR_le c (v s q) q
        rwa [hv0] at this
    _ = ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
          (2 * (2 * gev (CkM * IM) AkM j) * gev CPhi Achi (c - j)) := by
        have hmi : Measurable fun s : Unit → ℝ =>
            (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (X₀ + ε * s ()) :=
          (measurable_const.indicator measurableSet_Icc).comp
            (measurable_const.add (measurable_const.mul (measurable_pi_apply ())))
        have hmq : ∀ j, Measurable fun q : ℝ × ℝ => (1 + ‖q.1‖ₑ) * gM j q := fun j =>
          (measurable_const.add measurable_fst.enorm).mul (measurable_gM j)
        rw [lintegral_lintegral_finsetSum _ fun j _ =>
          measurable_const.mul (((hmi.comp measurable_snd).mul (measurable_const.mul
            ((hmq j).comp measurable_fst))).mul measurable_const)]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hin : ∀ q : ℝ × ℝ, ∫⁻ s : Unit → ℝ, (c.choose j : ℝ≥0∞) *
            ((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (X₀ + ε * s ()) *
              (2 * ((1 + ‖q.1‖ₑ) * gM j q)) * gev CPhi Achi (c - j)) =
            ((c.choose j : ℝ≥0∞) * (2 * 2) * gev CPhi Achi (c - j)) *
              ((1 + ‖q.1‖ₑ) * gM j q) := fun q => by
          have : ∀ s : Unit → ℝ, (c.choose j : ℝ≥0∞) *
              ((Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (X₀ + ε * s ()) *
                (2 * ((1 + ‖q.1‖ₑ) * gM j q)) * gev CPhi Achi (c - j)) =
              ((c.choose j : ℝ≥0∞) * (2 * ((1 + ‖q.1‖ₑ) * gM j q)) * gev CPhi Achi (c - j)) *
                (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) (X₀ + ε * s ()) :=
            fun s => by ring
          simp_rw [this]
          rw [lintegral_const_mul _ hmi, hind]
          ring
        simp_rw [hin]
        rw [lintegral_const_mul _ (hmq j), lintegral_gM_weight]
        ring
    _ ≤ gev (16 * (CkM * IM) * CPhi) A c := by
        have hC : 0 ≤ CkM * IM := mul_nonneg kerM_bound.1 IM_nonneg
        have h1 : ∀ j, gev (CkM * IM) AkM j ≤ gev (CkM * IM) A j := fun j =>
          gev_mono le_rfl kerM_bound.2.1 (AkM_le_A0.trans hA) hC j
        have h2 : ∀ j, gev CPhi Achi j ≤ gev CPhi A j := fun j =>
          gev_mono le_rfl Achi_nonneg (Achi_le_A0.trans hA) CPhi_nonneg j
        have hconv := gev_conv_le hC CPhi_nonneg hA0 h1 h2 c
        calc ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
              (2 * (2 * gev (CkM * IM) AkM j) * gev CPhi Achi (c - j))
            = 4 * ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * gev (CkM * IM) AkM j *
                gev CPhi Achi (c - j) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
          _ ≤ 4 * gev (4 * (CkM * IM) * CPhi) A c := mul_le_mul' le_rfl hconv
          _ = gev (16 * (CkM * IM) * CPhi) A c := by
              rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, gev_mul_const 4 (by norm_num)]
              ring_nf

end Gamma

end WaveTurbulence.ClassJR
