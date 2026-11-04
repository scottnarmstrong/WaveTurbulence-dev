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

omit [Fintype ι₁] [Fintype ι₂] in
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
theorem gamma_KMR_le {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (X₀ : ℝ)
    (v : (Unit → ℝ) → ℝ × ℝ → Fin 2 → ℝ) (hv0 : ∀ s q, v s q 0 = X₀ + ε * s ())
    (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
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

/-- `(A^θ + 2B^θ + 1) A⁻¹ B⁻¹ ≤ 2 A^{θ-1} B⁻¹ + 2 B^{θ-1} A⁻¹` for `A, B ≥ 1`. -/
theorem weight_decay_le {θ : ℝ} (h0 : 0 ≤ θ) (a b : ℝ) :
    ((1 + |a|) ^ θ + 2 * (1 + |b|) ^ θ + 1) * ((1 + |a|)⁻¹ * (1 + |b|)⁻¹) ≤
      2 * ((1 + |a|) ^ (θ - 1) * (1 + |b|) ^ (-1 : ℝ)) +
        2 * ((1 + |b|) ^ (θ - 1) * (1 + |a|) ^ (-1 : ℝ)) := by
  have hA : 1 ≤ 1 + |a| := by linarith [abs_nonneg a]
  have hB : 1 ≤ 1 + |b| := by linarith [abs_nonneg b]
  have hA0 : 0 < 1 + |a| := by linarith
  have hB0 : 0 < 1 + |b| := by linarith
  have eA : (1 + |a|) ^ θ * (1 + |a|)⁻¹ = (1 + |a|) ^ (θ - 1) := by
    rw [Real.rpow_sub_one hA0.ne']; field_simp
  have eB : (1 + |b|) ^ θ * (1 + |b|)⁻¹ = (1 + |b|) ^ (θ - 1) := by
    rw [Real.rpow_sub_one hB0.ne']; field_simp
  have iA : (1 + |a|)⁻¹ = (1 + |a|) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
  have iB : (1 + |b|)⁻¹ = (1 + |b|) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
  have hle : (1 + |a|) ^ (-1 : ℝ) ≤ (1 + |a|) ^ (θ - 1) :=
    Real.rpow_le_rpow_of_exponent_le hA (by linarith)
  have hBpos : 0 ≤ (1 + |b|) ^ (-1 : ℝ) := by positivity
  calc ((1 + |a|) ^ θ + 2 * (1 + |b|) ^ θ + 1) * ((1 + |a|)⁻¹ * (1 + |b|)⁻¹)
      = ((1 + |a|) ^ θ * (1 + |a|)⁻¹) * (1 + |b|)⁻¹ +
          2 * (((1 + |b|) ^ θ * (1 + |b|)⁻¹) * (1 + |a|)⁻¹) +
            (1 + |a|)⁻¹ * (1 + |b|)⁻¹ := by ring
    _ = (1 + |a|) ^ (θ - 1) * (1 + |b|) ^ (-1 : ℝ) +
          2 * ((1 + |b|) ^ (θ - 1) * (1 + |a|) ^ (-1 : ℝ)) +
            (1 + |a|) ^ (-1 : ℝ) * (1 + |b|) ^ (-1 : ℝ) := by rw [eA, eB, ← iA, ← iB]
    _ ≤ (1 + |a|) ^ (θ - 1) * (1 + |b|) ^ (-1 : ℝ) +
          2 * ((1 + |b|) ^ (θ - 1) * (1 + |a|) ^ (-1 : ℝ)) +
            (1 + |a|) ^ (θ - 1) * (1 + |b|) ^ (-1 : ℝ) := by gcongr
    _ ≤ _ := by
        have : 0 ≤ (1 + |a|) ^ (θ - 1) * (1 + |b|) ^ (-1 : ℝ) := by positivity
        linarith

/-- The pointwise bound of the `χ_∞` couplings of `J R`. -/
theorem enorm_iteratedFDeriv_KPR_le {θ : ℝ} (h0 : 0 ≤ θ) (c : ℕ) (x : Fin 2 → ℝ) (q : Unit) :
    ((1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1) *
      ‖iteratedFDeriv ℝ c (fun x => KPR x q) x‖ₑ ≤
      ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * (gev CPhi Achi j * gev CPhi Achi (c - j) *
        (2 * ENNReal.ofReal ((1 + |x 0|) ^ (θ - 1) * (1 + |x 1|) ^ (-1 : ℝ)) +
          2 * ENNReal.ofReal ((1 + |x 1|) ^ (θ - 1) * (1 + |x 0|) ^ (-1 : ℝ)))) := by
  rw [KPR_eq]
  refine (mul_le_mul' le_rfl (enorm_iteratedFDeriv_prod2_le contDiff_phiR
    contDiff_chiInvRc c x)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 := enorm_iteratedDeriv_phiR_le' j (x 0)
  have h2 := enorm_iteratedDeriv_chiInvRc_le (c - j) (x 1)
  have hw : (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1 =
      ENNReal.ofReal ((1 + |x 0|) ^ θ + 2 * (1 + |x 1|) ^ θ + 1) := by
    have e : ∀ y : ℝ, (1 : ℝ≥0∞) + ‖y‖ₑ = ENNReal.ofReal (1 + |y|) := fun y => by
      rw [ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one, ← Real.norm_eq_abs,
        ofReal_norm]
    rw [e, e, ENNReal.ofReal_rpow_of_nonneg (by positivity) h0,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) h0, ENNReal.ofReal_add (by positivity)
        zero_le_one, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_mul (by norm_num)]
    simp
  calc ((1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1) * ((c.choose j : ℝ≥0∞) *
        ‖iteratedDeriv j phiR (x 0)‖ₑ * ‖iteratedDeriv (c - j) (fun y => (chiInvR y : ℂ)) (x 1)‖ₑ)
      ≤ ((1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 1) * ((c.choose j : ℝ≥0∞) *
          (gev CPhi Achi j * ENNReal.ofReal ((1 + |x 0|)⁻¹)) *
          (gev CPhi Achi (c - j) * ENNReal.ofReal ((1 + |x 1|)⁻¹))) := by gcongr
    _ = (c.choose j : ℝ≥0∞) * (gev CPhi Achi j * gev CPhi Achi (c - j) *
          ENNReal.ofReal (((1 + |x 0|) ^ θ + 2 * (1 + |x 1|) ^ θ + 1) *
            ((1 + |x 0|)⁻¹ * (1 + |x 1|)⁻¹))) := by
        rw [hw, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring
    _ ≤ _ := by
        gcongr
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
        exact ENNReal.ofReal_le_ofReal (weight_decay_le h0 (x 0) (x 1))

/-- **`Γ` for the `χ_∞` pieces of `J R`** (DH21 L1014; DH23 L966–L969). -/
theorem gamma_KPR_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {ε₀ ε₁ : ℤ} (hε₀ : ε₀ = 1 ∨ ε₀ = -1)
    (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (X₀ X₁ : ℝ) (v : (Unit → ℝ) → Unit → Fin 2 → ℝ) (hv0 : ∀ s q, v s q 0 = X₀ + ε₀ * s ())
    (hv1 : ∀ s q, v s q 1 = X₁ + ε₁ * s ()) (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q : Unit, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 0‖ₑ) ^ θ + 2 * (1 + ‖v s q 1‖ₑ) ^ θ + 1) *
      ‖iteratedFDeriv ℝ c (fun x => KPR x q) (v s q)‖ₑ ≤
        gev (16 * Cθ θ * (CPhi * CPhi)) A c := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hε₀' : (ε₀ : ℝ) = 1 ∨ (ε₀ : ℝ) = -1 := by rcases hε₀ with rfl | rfl <;> simp
  have hε₁' : (ε₁ : ℝ) = 1 ∨ (ε₁ : ℝ) = -1 := by rcases hε₁ with rfl | rfl <;> simp
  have hC := Cθ_nonneg h0 h1
  set D : ℝ → ℝ → ℝ := fun a b => (1 + |a|) ^ (θ - 1) * (1 + |b|) ^ (-1 : ℝ) with hD
  have hDm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (D p.1 p.2) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_const.add (continuous_abs.measurable.comp measurable_fst)).pow_const _).mul
        ((measurable_const.add (continuous_abs.measurable.comp measurable_snd)).pow_const _))
  have hint : ∀ (Y₀ Y₁ : ℝ) {a b : ℝ}, (a = 1 ∨ a = -1) → (b = 1 ∨ b = -1) →
      ∫⁻ s : Unit → ℝ, ENNReal.ofReal (D (Y₀ + a * s ()) (Y₁ + b * s ())) ≤
        ENNReal.ofReal (Cθ θ) := fun Y₀ Y₁ a b ha hb => by
    rw [lintegral_unitFun (G := fun t => ENNReal.ofReal (D (Y₀ + a * t) (Y₁ + b * t)))]
    exact lintegral_decay_signs h0 h1 ha hb Y₀ Y₁
  have hlin : ∀ (Y : ℝ) (a : ℝ), Measurable fun s : Unit → ℝ => (1 + |Y + a * s ()|) :=
    fun Y a => measurable_const.add (continuous_abs.measurable.comp
      (measurable_const.add (measurable_const.mul (measurable_pi_apply ()))))
  have hmD : ∀ (Y₀ Y₁ a b : ℝ), Measurable fun s : Unit → ℝ =>
      ENNReal.ofReal (D (Y₀ + a * s ()) (Y₁ + b * s ())) := fun Y₀ Y₁ a b => by
    simp only [hD]
    exact ENNReal.measurable_ofReal.comp
      (((hlin Y₀ a).pow_const _).mul ((hlin Y₁ b).pow_const _))
  calc ∫⁻ q : Unit, ∫⁻ s : Unit → ℝ, ((1 + ‖v s q 0‖ₑ) ^ θ + 2 * (1 + ‖v s q 1‖ₑ) ^ θ + 1) *
        ‖iteratedFDeriv ℝ c (fun x => KPR x q) (v s q)‖ₑ
      ≤ ∫⁻ q : Unit, ∫⁻ s : Unit → ℝ, ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
          (gev CPhi Achi j * gev CPhi Achi (c - j) *
            (2 * ENNReal.ofReal (D (X₀ + ε₀ * s ()) (X₁ + ε₁ * s ())) +
              2 * ENNReal.ofReal (D (X₁ + ε₁ * s ()) (X₀ + ε₀ * s ())))) := by
        refine lintegral_mono fun q => lintegral_mono fun s => ?_
        have := enorm_iteratedFDeriv_KPR_le h0 c (v s q) q
        rw [hv0, hv1] at this
        rw [hv0, hv1]
        simpa only [hD] using this
    _ ≤ ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
          (gev CPhi Achi j * gev CPhi Achi (c - j) * (4 * ENNReal.ofReal (Cθ θ))) := by
        rw [show (volume : Measure Unit) = Measure.dirac () from rfl, lintegral_dirac]
        have hm2 : Measurable fun s : Unit → ℝ =>
            2 * ENNReal.ofReal (D (X₀ + ε₀ * s ()) (X₁ + ε₁ * s ())) +
              2 * ENNReal.ofReal (D (X₁ + ε₁ * s ()) (X₀ + ε₀ * s ())) :=
          ((hmD _ _ _ _).const_mul 2).add ((hmD _ _ _ _).const_mul 2)
        rw [lintegral_finsetSum _ fun j _ => (hm2.const_mul _).const_mul _]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [lintegral_const_mul _ (hm2.const_mul _), lintegral_const_mul _ hm2,
          lintegral_add_left ((hmD _ _ _ _).const_mul 2),
          lintegral_const_mul _ (hmD _ _ _ _), lintegral_const_mul _ (hmD _ _ _ _)]
        gcongr
        exact (add_le_add (mul_le_mul' le_rfl (hint _ _ hε₀' hε₁'))
          (mul_le_mul' le_rfl (hint _ _ hε₁' hε₀'))).trans_eq (by ring)
    _ ≤ gev (16 * Cθ θ * (CPhi * CPhi)) A c := by
        have h2 : ∀ j, gev CPhi Achi j ≤ gev CPhi A j := fun j =>
          gev_mono le_rfl Achi_nonneg (Achi_le_A0.trans hA) CPhi_nonneg j
        have hconv := gev_conv_le CPhi_nonneg CPhi_nonneg hA0 h2 h2 c
        calc ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
              (gev CPhi Achi j * gev CPhi Achi (c - j) * (4 * ENNReal.ofReal (Cθ θ)))
            = ENNReal.ofReal (4 * Cθ θ) * ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
                gev CPhi Achi j * gev CPhi Achi (c - j) := by
              rw [Finset.mul_sum, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
          _ ≤ ENNReal.ofReal (4 * Cθ θ) * gev (4 * CPhi * CPhi) A c := mul_le_mul' le_rfl hconv
          _ = gev (16 * Cθ θ * (CPhi * CPhi)) A c := by
              rw [gev_mul_const _ (by positivity)]
              ring_nf

end Gamma

end WaveTurbulence.ClassJR
