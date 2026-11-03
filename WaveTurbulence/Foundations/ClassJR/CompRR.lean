/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.CompRJ
public import WaveTurbulence.Foundations.ClassJR.CouplingRR

/-!
# DH21 Lemma 5.5, `R R`: set-up, couplings and weight splits

For `ℛ^{(1)} = ∫ m^{(1)} R_{ℓ₁+ε₁α₁, ℓ₂+ε₁α₁; γ₁,γ₂,γ₃}` and
`ℛ^{(2)} = ∫ m^{(2)} R_{ℓ₃+ε₂α₂, ℓ₄+ε₂α₂; γ₄,γ₅,γ₆}`, the composition kernel is (DH21 L1027–L1033)
`χ_∞(x₁)/x₁ · χ_∞(x₂)/x₂ · J_{ℓ₂+ε₁α₁;γ₁,γ₂} J_{ℓ₄+ε₂α₂;γ₄,γ₅}` with `x₁ = ℓ₁ + ε₁α₁ + γ₃`,
`x₂ = ℓ₃ + ε₂α₂ + γ₆`, and the `J J` split gives three pieces with
`x₀ = ℓ₄ - ℓ₂ + ε₂α₂ - ε₁α₁ + γ₂ + γ₄`:

* `χ₀` piece: `kerM(x₀) χ_∞(x₁)/x₁ χ_∞(x₂)/x₂`, bundle `ℓ₂ + ε₁α₁`,
  `γ' = (γ₁ + σ, γ₂ + γ₄ + γ₅ - σ)`;
* `χ_∞` pieces: `±Φ(x₀) χ_∞(x₁)/x₁ χ_∞(x₂)/x₂`, bundles `ℓ₄ + ε₂α₂` and `ℓ₂ + ε₁α₁`.

The variables are `α ∈ (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ`, the special variables being `α (inr 0) = α₁` and
`α (inr 1) = α₂`. The integration variables `((γ₁,(γ₂,γ₃)),((γ₄,(γ₅,γ₆)),q))` are brought by
`eRR` to `((γ₁,γ₅),((γ₂,γ₄),(γ₃,(γ₆,q))))`. The weight of the composed operator is split using
the denominators `x₁`, `x₂` for `|α₁|^θ`, `|α₂|^θ` and `x₀` for `|γ₂ + γ₄|^θ` (DH21 L1041); the
coupling integrals over `(α₁, α₂)` are `lintegral_tri3_le`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

section Equiv

variable (Q : Type*) [MeasureSpace Q] [SFinite (volume : Measure Q)]

/-- `((γ₁,(γ₂,γ₃)),((γ₄,(γ₅,γ₆)),q)) ↦ ((γ₁,γ₅),((γ₂,γ₄),(γ₃,(γ₆,q))))`. -/
@[expose] def eRR : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Q) ≃ᵐ
    (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × (ℝ × Q))) where
  toFun z := ((z.1.1, z.2.1.2.1), ((z.1.2.1, z.2.1.1), (z.1.2.2, (z.2.1.2.2, z.2.2))))
  invFun z := ((z.1.1, (z.2.1.1, z.2.2.1)), ((z.2.1.2, (z.1.2, z.2.2.2.1)), z.2.2.2.2))
  left_inv z := rfl
  right_inv z := rfl
  measurable_toFun := by
    change Measurable fun z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Q) =>
      ((z.1.1, z.2.1.2.1), ((z.1.2.1, z.2.1.1), (z.1.2.2, (z.2.1.2.2, z.2.2))))
    fun_prop
  measurable_invFun := by
    change Measurable fun z : (ℝ × ℝ) × ((ℝ × ℝ) × (ℝ × (ℝ × Q))) =>
      ((z.1.1, (z.2.1.1, z.2.2.1)), ((z.2.1.2, (z.1.2, z.2.2.2.1)), z.2.2.2.2))
    fun_prop

omit [SFinite (volume : Measure Q)] in
@[simp] theorem eRR_apply (z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Q)) :
    eRR Q z = ((z.1.1, z.2.1.2.1), ((z.1.2.1, z.2.1.1), (z.1.2.2, (z.2.1.2.2, z.2.2)))) := rfl

theorem measurePreserving_eRR : MeasurePreserving (eRR Q) := by
  have k1 : MeasurePreserving (Prod.map
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ)).symm (id : Q → Q)) :=
    MeasurePreserving.prod volume_preserving_prodAssoc.symm (MeasurePreserving.id volume)
  have k2 := volume_preserving_prodAssoc (α₁ := ℝ × ℝ) (β₁ := ℝ) (γ₁ := Q)
  have h : MeasurePreserving (Prod.map (id : ℝ × (ℝ × ℝ) → ℝ × (ℝ × ℝ))
      ((MeasurableEquiv.prodAssoc (α := ℝ × ℝ) (β := ℝ) (γ := Q)) ∘
        Prod.map (MeasurableEquiv.prodAssoc (α := ℝ) (β := ℝ) (γ := ℝ)).symm (id : Q → Q))) :=
    MeasurePreserving.prod (MeasurePreserving.id volume) (k2.comp k1)
  have := (measurePreserving_eRJ (ℝ × Q)).comp h
  convert this using 1
  funext z
  rfl

end Equiv

/-- The shift of the `χ₀` piece of `R R` in the layout `η = ((γ₂,γ₄),(γ₃,(γ₆,q)))`. -/
@[expose] def bMRR (η : (ℝ × ℝ) × (ℝ × (ℝ × (ℝ × ℝ)))) : ℝ × ℝ :=
  (η.2.2.2.1, η.1.1 + η.1.2 - η.2.2.2.1)

/-- The shift of the first `χ_∞` piece of `R R`. -/
@[expose] def bP1RR (η : (ℝ × ℝ) × (ℝ × (ℝ × Unit))) : ℝ × ℝ := (η.1.1 + η.1.2, 0)

/-- The shift of the second `χ_∞` piece of `R R`. -/
@[expose] def bP2RR (η : (ℝ × ℝ) × (ℝ × (ℝ × Unit))) : ℝ × ℝ := (0, η.1.1 + η.1.2)

theorem measurable_bMRR : Measurable bMRR := by unfold bMRR; fun_prop
theorem measurable_bP1RR : Measurable bP1RR := by unfold bP1RR; fun_prop
theorem measurable_bP2RR : Measurable bP2RR := by unfold bP2RR; fun_prop

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

section Bundles

/-- A bundle on `(ι₁ ⊕ ι₂) ⊕ Fin 2` from its four blocks. -/
@[expose] def y4 (f : ι₁ → ℤ) (g : ι₂ → ℤ) (e₀ e₁ : ℤ) : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℤ :=
  Sum.elim (Sum.elim f g) ![e₀, e₁]

theorem isBundle_y4 {f : ι₁ → ℤ} {g : ι₂ → ℤ} {e₀ e₁ : ℤ} (hf : IsBundle f) (hg : IsBundle g)
    (he₀ : |e₀| ≤ 1) (he₁ : |e₁| ≤ 1) : IsBundle (y4 f g e₀ e₁) := by
  rintro ((i | i) | r)
  · exact hf i
  · exact hg i
  · fin_cases r
    · simpa [y4] using he₀
    · simpa [y4] using he₁

theorem bundle_y4 (f : ι₁ → ℤ) (g : ι₂ → ℤ) (e₀ e₁ : ℤ) (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) :
    bundle (y4 f g e₀ e₁) α = bundle f (vA α) + bundle g (vB α) + e₀ * α (Sum.inr 0) +
      e₁ * α (Sum.inr 1) := by
  simp only [bundle, y4, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, vA, vB]
  ring

theorem sum_enorm_y4 (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) :
    ∑ j, ‖α j‖ₑ = ∑ i, ‖vA α i‖ₑ + ∑ i, ‖vB α i‖ₑ + ‖α (Sum.inr 0)‖ₑ +
      ‖α (Sum.inr 1)‖ₑ := by
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, vA, vB]
  ring

end Bundles

section Data

/-- The three forms `x₀ = ℓ₄ - ℓ₂ - ε₁α₁ + ε₂α₂ (+ γ₂ + γ₄)`, `x₁ = ℓ₁ + ε₁α₁ (+ γ₃)`,
`x₂ = ℓ₃ + ε₂α₂ (+ γ₆)`. -/
@[expose] def LsRR (R₁ : RSym ι₁) (R₂ : RSym ι₂) : Fin 3 → (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℤ :=
  ![y4 (fun i => -R₁.y₂ i) R₂.y₂ (-R₁.ε) R₂.ε, y4 R₁.y₁ 0 R₁.ε 0, y4 0 R₂.y₁ 0 R₂.ε]

/-- The constant parts `γ₂ + γ₄`, `γ₃`, `γ₆` of the three forms. -/
@[expose] def csRR (Q : Type*) : Fin 3 → (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Q) → ℝ :=
  ![fun z => z.1.2.1 + z.2.1.1, fun z => z.1.2.2, fun z => z.2.1.2.2]

variable {R₁ : RSym ι₁} {R₂ : RSym ι₂}

theorem isBundle_LsRR {θ A N₁ N₂ : ℝ} (h₁ : R₁.Bound θ A N₁) (h₂ : R₂.Bound θ A N₂) :
    ∀ r, IsBundle (LsRR R₁ R₂ r) := by
  intro r; fin_cases r
  · exact isBundle_y4 (isBundle_neg h₁.bundle₂) h₂.bundle₂ (abs_sign_le (sign_neg h₁.sign))
      (abs_sign_le h₂.sign)
  · exact isBundle_y4 h₁.bundle₁ isBundle_zero (abs_sign_le h₁.sign) (by simp)
  · exact isBundle_y4 isBundle_zero h₂.bundle₁ (by simp) (abs_sign_le h₂.sign)

theorem measurable_csRR (Q : Type*) [MeasurableSpace Q] : ∀ r, Measurable (csRR Q r) := by
  intro r; fin_cases r
  · simp only [csRR]; exact (measurable_fst.comp (measurable_snd.comp measurable_fst)).add
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
  · simp only [csRR]
    exact measurable_snd.comp (measurable_snd.comp measurable_fst)
  · simp only [csRR]
    exact measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_snd))

theorem formsV_RR_zero {Q : Type*} (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ)
    (z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Q)) :
    formsV (LsRR R₁ R₂) (csRR Q) α z 0 =
      bundle R₂.y₂ (vB α) - bundle R₁.y₂ (vA α) + (z.1.2.1 + z.2.1.1) -
        R₁.ε * α (Sum.inr 0) + R₂.ε * α (Sum.inr 1) := by
  simp only [formsV, LsRR, csRR, Matrix.cons_val, bundle_y4]
  have : bundle (fun i => -R₁.y₂ i) (vA α) = -bundle R₁.y₂ (vA α) := by
    simp [bundle, Finset.sum_neg_distrib]
  rw [this]
  push_cast
  ring

theorem formsV_RR_one {Q : Type*} (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ)
    (z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Q)) :
    formsV (LsRR R₁ R₂) (csRR Q) α z 1 =
      bundle R₁.y₁ (vA α) + z.1.2.2 + R₁.ε * α (Sum.inr 0) := by
  simp only [formsV, LsRR, csRR, Matrix.cons_val, bundle_y4]
  have : bundle (0 : ι₂ → ℤ) (vB α) = 0 := by simp [bundle]
  rw [this]
  push_cast
  ring

theorem formsV_RR_two {Q : Type*} (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ)
    (z : (ℝ × (ℝ × ℝ)) × ((ℝ × (ℝ × ℝ)) × Q)) :
    formsV (LsRR R₁ R₂) (csRR Q) α z 2 =
      bundle R₂.y₁ (vB α) + z.2.1.2.2 + R₂.ε * α (Sum.inr 1) := by
  simp only [formsV, LsRR, csRR, Matrix.cons_val, bundle_y4]
  have : bundle (0 : ι₁ → ℤ) (vA α) = 0 := by simp [bundle]
  rw [this]
  push_cast
  ring

theorem vS_elim2 (a : ι₁ ⊕ ι₂ → ℝ) (s : Fin 2 → ℝ) (r : Fin 2) :
    (Sum.elim a s : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) (Sum.inr r) = s r := rfl

end Data

section Couplings

/-- The coupling `kerM(x₀) χ_∞(x₁)/x₁ χ_∞(x₂)/x₂` of the `χ₀` piece of `R R`. -/
@[expose] noncomputable def KMRR (x : Fin 3 → ℝ) (q : ℝ × ℝ) : ℂ :=
  kerM (x 0) q * ((chiInvR (x 1) : ℂ) * (chiInvR (x 2) : ℂ))

/-- The coupling `Φ(x₀) χ_∞(x₁)/x₁ χ_∞(x₂)/x₂` of the `χ_∞` pieces of `R R`. -/
@[expose] noncomputable def KPRR (x : Fin 3 → ℝ) (_ : Unit) : ℂ :=
  phiR (x 0) * ((chiInvR (x 1) : ℂ) * (chiInvR (x 2) : ℂ))

/-- The coupling `-Φ(x₀) χ_∞(x₁)/x₁ χ_∞(x₂)/x₂`. -/
@[expose] noncomputable def KPRRn (x : Fin 3 → ℝ) (_ : Unit) : ℂ :=
  -(phiR (x 0) * ((chiInvR (x 1) : ℂ) * (chiInvR (x 2) : ℂ)))

theorem KMRR_eq (q : ℝ × ℝ) : (fun x => KMRR x q) =
    prod3 (fun y => kerM y q) (fun y => (chiInvR y : ℂ)) fun y => (chiInvR y : ℂ) := rfl

theorem KPRR_eq (q : Unit) : (fun x => KPRR x q) =
    prod3 phiR (fun y => (chiInvR y : ℂ)) fun y => (chiInvR y : ℂ) := rfl

theorem contDiff_KMRR (q : ℝ × ℝ) : ContDiff ℝ ∞ fun x => KMRR x q := by
  rw [KMRR_eq]; exact contDiff_prod3 (contDiff_kerM q) contDiff_chiInvRc contDiff_chiInvRc

theorem contDiff_KPRR (q : Unit) : ContDiff ℝ ∞ fun x => KPRR x q := by
  rw [KPRR_eq]; exact contDiff_prod3 contDiff_phiR contDiff_chiInvRc contDiff_chiInvRc

theorem contDiff_KPRRn (q : Unit) : ContDiff ℝ ∞ fun x => KPRRn x q :=
  (contDiff_KPRR q).neg

theorem KPRRn_iteratedFDeriv (c : ℕ) (x : Fin 3 → ℝ) (q : Unit) :
    ‖iteratedFDeriv ℝ c (fun x => KPRRn x q) x‖ₑ =
      ‖iteratedFDeriv ℝ c (fun x => KPRR x q) x‖ₑ := by
  rw [show (fun x => KPRRn x q) = -(fun x => KPRR x q) from rfl, iteratedFDeriv_neg,
    Pi.neg_apply, enorm_neg]

theorem measurable_KMRR : Measurable (Function.uncurry KMRR) := by
  have hmap : Measurable fun p : (Fin 3 → ℝ) × (ℝ × ℝ) => ((p.1 0, p.2) : ℝ × (ℝ × ℝ)) :=
    ((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd
  have h1 := measurable_kerM.comp hmap
  have h' : Measurable fun y : ℝ => (chiInvR y : ℂ) := contDiff_chiInvRc.continuous.measurable
  have h2 : Measurable fun p : (Fin 3 → ℝ) × (ℝ × ℝ) => (chiInvR (p.1 1) : ℂ) :=
    h'.comp ((measurable_pi_apply 1).comp measurable_fst)
  have h3 : Measurable fun p : (Fin 3 → ℝ) × (ℝ × ℝ) => (chiInvR (p.1 2) : ℂ) :=
    h'.comp ((measurable_pi_apply 2).comp measurable_fst)
  have e : Function.uncurry KMRR = fun p : (Fin 3 → ℝ) × (ℝ × ℝ) =>
      (Function.uncurry kerM ∘ fun p : (Fin 3 → ℝ) × (ℝ × ℝ) =>
        ((p.1 0, p.2) : ℝ × (ℝ × ℝ))) p * ((chiInvR (p.1 1) : ℂ) * (chiInvR (p.1 2) : ℂ)) := by
    funext p
    simp only [Function.uncurry, KMRR, Function.comp_apply]
  rw [e]
  exact h1.mul (h2.mul h3)

theorem measurable_KPRR : Measurable (Function.uncurry KPRR) := by
  have h' : Measurable fun y : ℝ => (chiInvR y : ℂ) := contDiff_chiInvRc.continuous.measurable
  have hp : Measurable phiR := contDiff_phiR.continuous.measurable
  have e : Function.uncurry KPRR = fun p : (Fin 3 → ℝ) × Unit =>
      phiR (p.1 0) * ((chiInvR (p.1 1) : ℂ) * (chiInvR (p.1 2) : ℂ)) := by
    funext p; simp only [Function.uncurry, KPRR]
  rw [e]
  exact (hp.comp ((measurable_pi_apply 0).comp measurable_fst)).mul
    ((h'.comp ((measurable_pi_apply 1).comp measurable_fst)).mul
      (h'.comp ((measurable_pi_apply 2).comp measurable_fst)))

theorem measurable_KPRRn : Measurable (Function.uncurry KPRRn) := by
  have e : Function.uncurry KPRRn = fun p : (Fin 3 → ℝ) × Unit => -Function.uncurry KPRR p := by
    funext p; simp only [Function.uncurry, KPRRn, KPRR]
  rw [e]
  exact measurable_KPRR.neg

end Couplings

section Gamma

theorem indicator_le_two_inv (x : ℝ) :
    (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) x ≤ 2 * ENNReal.ofReal ((1 + |x|)⁻¹) := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    have : |x| ≤ 1 := abs_le.2 hx
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  · rw [Set.indicator_of_notMem hx]; exact bot_le

theorem one_add_enorm_eq (y : ℝ) : (1 : ℝ≥0∞) + ‖y‖ₑ = ENNReal.ofReal (1 + |y|) := by
  rw [ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one, ← Real.norm_eq_abs,
    ofReal_norm]

theorem one_le_one_add_rpow {θ : ℝ} (h0 : 0 ≤ θ) (y : ℝ≥0∞) : 1 ≤ (1 + y) ^ θ := by
  rcases h0.eq_or_lt with rfl | hθ
  · simp
  · exact ENNReal.one_le_rpow le_self_add hθ

/-- `V(x) ρ(x₀) ρ(x₁) ρ(x₂) = tri3`. -/
theorem V_mul_rho_eq {θ : ℝ} (h0 : 0 ≤ θ) (x0 x1 x2 : ℝ) :
    ((1 + ‖x0‖ₑ) ^ θ + (1 + ‖x1‖ₑ) ^ θ + (1 + ‖x2‖ₑ) ^ θ) *
      (ENNReal.ofReal ((1 + |x0|)⁻¹) * ENNReal.ofReal ((1 + |x1|)⁻¹) *
        ENNReal.ofReal ((1 + |x2|)⁻¹)) = ENNReal.ofReal (tri3 θ x0 x1 x2) := by
  rw [one_add_enorm_eq, one_add_enorm_eq, one_add_enorm_eq,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) h0,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) h0,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) h0,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e : ∀ y : ℝ, (1 + |y|) ^ (-(1 - θ)) = (1 + |y|) ^ θ * (1 + |y|)⁻¹ := fun y => by
    have hy : 0 < 1 + |y| := by positivity
    rw [show -(1 - θ) = θ + (-1) by ring, Real.rpow_add hy, Real.rpow_neg_one]
  unfold tri3
  rw [e x0, e x1, e x2]
  simp only [Real.rpow_neg_one]
  ring

/-- The weight of the `χ₀` coupling of `R R`. -/
@[expose] noncomputable def wMRR (θ : ℝ) (x : Fin 3 → ℝ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  (1 + ‖x 1‖ₑ) ^ θ + (1 + ‖x 2‖ₑ) ^ θ + (1 + ‖q.1‖ₑ)

/-- The `q`-dependent factor of the bound of the `χ₀` coupling of `R R`. -/
@[expose] noncomputable def GMRR (c : ℕ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * (2 * ((1 + ‖q.1‖ₑ) * gM j q)) *
    ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) * gev CPhi Achi i *
      gev CPhi Achi (c - j - i)

theorem measurable_GMRR (c : ℕ) : Measurable (GMRR c) :=
  Finset.measurable_sum _ fun j _ => (measurable_const.mul (((measurable_const.add
    measurable_fst.enorm).mul (measurable_gM j)).const_mul 2)).mul_const _

/-- The pointwise bound of the `χ₀` coupling of `R R`. -/
theorem enorm_iteratedFDeriv_KMRR_le {θ : ℝ} (h0 : 0 ≤ θ) (c : ℕ) (x : Fin 3 → ℝ)
    (q : ℝ × ℝ) :
    wMRR θ x q * ‖iteratedFDeriv ℝ c (fun x => KMRR x q) x‖ₑ ≤
      GMRR c q * ENNReal.ofReal (tri3 θ (x 0) (x 1) (x 2)) := by
  set V := (1 + ‖x 0‖ₑ) ^ θ + (1 + ‖x 1‖ₑ) ^ θ + (1 + ‖x 2‖ₑ) ^ θ with hV
  have hw : wMRR θ x q ≤ (1 + ‖q.1‖ₑ) * V := by
    have h1 : (1 : ℝ≥0∞) ≤ 1 + ‖q.1‖ₑ := le_self_add
    unfold wMRR
    calc (1 + ‖x 1‖ₑ) ^ θ + (1 + ‖x 2‖ₑ) ^ θ + (1 + ‖q.1‖ₑ)
        ≤ (1 + ‖q.1‖ₑ) * (1 + ‖x 1‖ₑ) ^ θ + (1 + ‖q.1‖ₑ) * (1 + ‖x 2‖ₑ) ^ θ +
            (1 + ‖q.1‖ₑ) * (1 + ‖x 0‖ₑ) ^ θ :=
          add_le_add (add_le_add (le_mul_of_one_le_left bot_le h1)
            (le_mul_of_one_le_left bot_le h1))
            (le_mul_of_one_le_right bot_le (one_le_one_add_rpow h0 _))
      _ = (1 + ‖q.1‖ₑ) * V := by rw [hV]; ring
  have hD : ‖iteratedFDeriv ℝ c (fun x => KMRR x q) x‖ₑ ≤
      ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
        (2 * ENNReal.ofReal ((1 + |x 0|)⁻¹) * gM j q) *
        ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) *
          (gev CPhi Achi i * ENNReal.ofReal ((1 + |x 1|)⁻¹)) *
          (gev CPhi Achi (c - j - i) * ENNReal.ofReal ((1 + |x 2|)⁻¹)) := by
    rw [KMRR_eq]
    refine (enorm_iteratedFDeriv_prod3_le (contDiff_kerM q) contDiff_chiInvRc contDiff_chiInvRc
      c x).trans (Finset.sum_le_sum fun j _ => ?_)
    refine mul_le_mul' (mul_le_mul' le_rfl ?_) (Finset.sum_le_sum fun i _ => ?_)
    · exact (enorm_iteratedDeriv_kerM_le_ind j (x 0) q).trans
        (mul_le_mul' (indicator_le_two_inv _) le_rfl)
    · exact mul_le_mul' (mul_le_mul' le_rfl (enorm_iteratedDeriv_chiInvRc_le i (x 1)))
        (enorm_iteratedDeriv_chiInvRc_le _ (x 2))
  rw [← V_mul_rho_eq h0]
  refine (mul_le_mul' hw hD).trans_eq ?_
  simp only [GMRR, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem lintegral_GMRR_le (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q, GMRR c q ≤ gev (32 * (CkM * IM) * (CPhi * CPhi)) A c := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have hC : 0 ≤ CkM * IM := mul_nonneg kerM_bound.1 IM_nonneg
  have hmq : ∀ j, Measurable fun q : ℝ × ℝ => (1 + ‖q.1‖ₑ) * gM j q := fun j =>
    (measurable_const.add measurable_fst.enorm).mul (measurable_gM j)
  unfold GMRR
  have hmj : ∀ j ∈ range (c + 1), Measurable fun q : ℝ × ℝ =>
      (c.choose j : ℝ≥0∞) * (2 * ((1 + ‖q.1‖ₑ) * gM j q)) *
        ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) * gev CPhi Achi i *
          gev CPhi Achi (c - j - i) := fun j _ =>
    (measurable_const.mul ((hmq j).const_mul 2)).mul_const _
  rw [lintegral_finsetSum _ hmj]
  have e : ∀ j ∈ range (c + 1), ∫⁻ q, (c.choose j : ℝ≥0∞) * (2 * ((1 + ‖q.1‖ₑ) * gM j q)) *
      ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) * gev CPhi Achi i *
        gev CPhi Achi (c - j - i) =
      (c.choose j : ℝ≥0∞) * (2 * gev (CkM * IM) AkM j) *
        ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) * gev CPhi Achi i *
          gev CPhi Achi (c - j - i) := fun j _ => by
    have m2 : Measurable fun q : ℝ × ℝ => 2 * ((1 + ‖q.1‖ₑ) * gM j q) := (hmq j).const_mul 2
    have m1 : Measurable fun q : ℝ × ℝ => (c.choose j : ℝ≥0∞) * (2 * ((1 + ‖q.1‖ₑ) * gM j q)) :=
      m2.const_mul _
    rw [lintegral_mul_const _ m1, lintegral_const_mul _ m2, lintegral_const_mul _ (hmq j),
      lintegral_gM_weight]
  rw [Finset.sum_congr rfl e]
  have h2 : ∀ j, gev CPhi Achi j ≤ gev CPhi A j := fun j =>
    gev_mono le_rfl Achi_nonneg (Achi_le_A0.trans hA) CPhi_nonneg j
  refine (gev_conv3_le (S₁ := fun j => 2 * gev (CkM * IM) AkM j) (S₂ := gev CPhi Achi)
    (S₃ := gev CPhi Achi) (N₁ := 2 * (CkM * IM)) (by positivity) CPhi_nonneg CPhi_nonneg hA0
    (fun j => ?_) h2 h2 c).trans_eq ?_
  · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, gev_mul_const _ (by norm_num)]
    exact gev_mono le_rfl kerM_bound.2.1 (AkM_le_A0.trans hA) (by positivity) j
  · congr 1; ring

/-- The constant of `gamma_KMRR_le`. -/
@[expose] noncomputable def NMRR (θ : ℝ) : ℝ := D3 θ * (32 * (CkM * IM) * (CPhi * CPhi))

theorem NMRR_nonneg (θ : ℝ) : 0 ≤ NMRR θ := by
  have := D3_nonneg θ; have := kerM_bound.1; have := IM_nonneg; have := CPhi_nonneg
  unfold NMRR; positivity

/-- **`Γ` for the `χ₀` piece of `R R`** (DH21 L1036–L1039). -/
theorem gamma_KMRR_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {e₁ e₂ : ℝ} (he₁ : e₁ = 1 ∨ e₁ = -1)
    (he₂ : e₂ = 1 ∨ e₂ = -1) (X₀ X₁ X₂ : ℝ) (v : (Fin 2 → ℝ) → ℝ × ℝ → Fin 3 → ℝ)
    (hv0 : ∀ s q, v s q 0 = X₀ - e₁ * s 0 + e₂ * s 1) (hv1 : ∀ s q, v s q 1 = X₁ + e₁ * s 0)
    (hv2 : ∀ s q, v s q 2 = X₂ + e₂ * s 1) (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q : ℝ × ℝ, ∫⁻ s : Fin 2 → ℝ, wMRR θ (v s q) q *
      ‖iteratedFDeriv ℝ c (fun x => KMRR x q) (v s q)‖ₑ ≤ gev (NMRR θ) A c := by
  have hmT : Measurable fun s : Fin 2 → ℝ => ENNReal.ofReal
      (tri3 θ (X₀ - e₁ * s 0 + e₂ * s 1) (X₁ + e₁ * s 0) (X₂ + e₂ * s 1)) := by
    unfold tri3; fun_prop
  calc ∫⁻ q : ℝ × ℝ, ∫⁻ s : Fin 2 → ℝ, wMRR θ (v s q) q *
        ‖iteratedFDeriv ℝ c (fun x => KMRR x q) (v s q)‖ₑ
      ≤ ∫⁻ q : ℝ × ℝ, ∫⁻ s : Fin 2 → ℝ, GMRR c q * ENNReal.ofReal
          (tri3 θ (X₀ - e₁ * s 0 + e₂ * s 1) (X₁ + e₁ * s 0) (X₂ + e₂ * s 1)) :=
        lintegral_mono fun q => lintegral_mono fun s => by
          have := enorm_iteratedFDeriv_KMRR_le h0 c (v s q) q
          rwa [hv0, hv1, hv2] at this
    _ = ∫⁻ q : ℝ × ℝ, GMRR c q * ∫⁻ s : Fin 2 → ℝ, ENNReal.ofReal
          (tri3 θ (X₀ - e₁ * s 0 + e₂ * s 1) (X₁ + e₁ * s 0) (X₂ + e₂ * s 1)) :=
        lintegral_congr fun q => lintegral_const_mul _ hmT
    _ ≤ ∫⁻ q : ℝ × ℝ, GMRR c q * ENNReal.ofReal (D3 θ) :=
        lintegral_mono fun q => mul_le_mul' le_rfl (lintegral_tri3_le h0 h1 he₁ he₂ X₀ X₁ X₂)
    _ = (∫⁻ q : ℝ × ℝ, GMRR c q) * ENNReal.ofReal (D3 θ) :=
        lintegral_mul_const _ (measurable_GMRR c)
    _ ≤ gev (32 * (CkM * IM) * (CPhi * CPhi)) A c * ENNReal.ofReal (D3 θ) :=
        mul_le_mul' (lintegral_GMRR_le c hA) le_rfl
    _ = gev (NMRR θ) A c := by rw [mul_comm, gev_mul_const _ (D3_nonneg θ)]; rfl

/-- The weight of the `χ_∞` couplings of `R R`. -/
@[expose] noncomputable def wPRR (θ : ℝ) (x : Fin 3 → ℝ) (_ : Unit) : ℝ≥0∞ :=
  (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 2 * (1 + ‖x 2‖ₑ) ^ θ + 1

/-- The factor of the bound of the `χ_∞` couplings of `R R`. -/
@[expose] noncomputable def GPRR (c : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) * gev CPhi Achi j *
    ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) * gev CPhi Achi i *
      gev CPhi Achi (c - j - i)

/-- The pointwise bound of the `χ_∞` couplings of `R R`. -/
theorem enorm_iteratedFDeriv_KPRR_le {θ : ℝ} (h0 : 0 ≤ θ) (c : ℕ) (x : Fin 3 → ℝ) (q : Unit) :
    wPRR θ x q * ‖iteratedFDeriv ℝ c (fun x => KPRR x q) x‖ₑ ≤
      2 * GPRR c * ENNReal.ofReal (tri3 θ (x 0) (x 1) (x 2)) := by
  set V := (1 + ‖x 0‖ₑ) ^ θ + (1 + ‖x 1‖ₑ) ^ θ + (1 + ‖x 2‖ₑ) ^ θ with hV
  have hw : wPRR θ x q ≤ 2 * V := by
    unfold wPRR
    calc (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 2 * (1 + ‖x 2‖ₑ) ^ θ + 1
        ≤ (1 + ‖x 0‖ₑ) ^ θ + 2 * (1 + ‖x 1‖ₑ) ^ θ + 2 * (1 + ‖x 2‖ₑ) ^ θ +
            (1 + ‖x 0‖ₑ) ^ θ := add_le_add le_rfl (one_le_one_add_rpow h0 _)
      _ = 2 * V := by rw [hV]; ring
  have hD : ‖iteratedFDeriv ℝ c (fun x => KPRR x q) x‖ₑ ≤
      ∑ j ∈ range (c + 1), (c.choose j : ℝ≥0∞) *
        (gev CPhi Achi j * ENNReal.ofReal ((1 + |x 0|)⁻¹)) *
        ∑ i ∈ range (c - j + 1), ((c - j).choose i : ℝ≥0∞) *
          (gev CPhi Achi i * ENNReal.ofReal ((1 + |x 1|)⁻¹)) *
          (gev CPhi Achi (c - j - i) * ENNReal.ofReal ((1 + |x 2|)⁻¹)) := by
    rw [KPRR_eq]
    refine (enorm_iteratedFDeriv_prod3_le contDiff_phiR contDiff_chiInvRc contDiff_chiInvRc
      c x).trans (Finset.sum_le_sum fun j _ => ?_)
    refine mul_le_mul' (mul_le_mul' le_rfl (enorm_iteratedDeriv_phiR_le' j (x 0)))
      (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul' (mul_le_mul' le_rfl (enorm_iteratedDeriv_chiInvRc_le i (x 1)))
      (enorm_iteratedDeriv_chiInvRc_le _ (x 2))
  rw [← V_mul_rho_eq h0]
  refine (mul_le_mul' hw hD).trans_eq ?_
  simp only [GPRR, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem GPRR_le (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    GPRR c ≤ gev (16 * CPhi * CPhi * CPhi) A c := by
  have hA0 : 0 ≤ A := A0_nonneg.trans hA
  have h2 : ∀ j, gev CPhi Achi j ≤ gev CPhi A j := fun j =>
    gev_mono le_rfl Achi_nonneg (Achi_le_A0.trans hA) CPhi_nonneg j
  exact gev_conv3_le CPhi_nonneg CPhi_nonneg CPhi_nonneg hA0 h2 h2 h2 c

/-- The constant of `gamma_KPRR_le`. -/
@[expose] noncomputable def NPRR (θ : ℝ) : ℝ := D3 θ * (32 * (CPhi * (CPhi * CPhi)))

theorem NPRR_nonneg (θ : ℝ) : 0 ≤ NPRR θ := by
  have := D3_nonneg θ; have := CPhi_nonneg
  unfold NPRR; positivity

/-- **`Γ` for the `χ_∞` pieces of `R R`** (DH21 L1039–L1041). -/
theorem gamma_KPRR_le {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {e₁ e₂ : ℝ} (he₁ : e₁ = 1 ∨ e₁ = -1)
    (he₂ : e₂ = 1 ∨ e₂ = -1) (X₀ X₁ X₂ : ℝ) (v : (Fin 2 → ℝ) → Unit → Fin 3 → ℝ)
    (hv0 : ∀ s q, v s q 0 = X₀ - e₁ * s 0 + e₂ * s 1) (hv1 : ∀ s q, v s q 1 = X₁ + e₁ * s 0)
    (hv2 : ∀ s q, v s q 2 = X₂ + e₂ * s 1) (c : ℕ) {A : ℝ} (hA : A0 ≤ A) :
    ∫⁻ q : Unit, ∫⁻ s : Fin 2 → ℝ, wPRR θ (v s q) q *
      ‖iteratedFDeriv ℝ c (fun x => KPRR x q) (v s q)‖ₑ ≤ gev (NPRR θ) A c := by
  have hmT : Measurable fun s : Fin 2 → ℝ => ENNReal.ofReal
      (tri3 θ (X₀ - e₁ * s 0 + e₂ * s 1) (X₁ + e₁ * s 0) (X₂ + e₂ * s 1)) := by
    unfold tri3; fun_prop
  rw [show (volume : Measure Unit) = Measure.dirac () from rfl, lintegral_dirac]
  calc ∫⁻ s : Fin 2 → ℝ, wPRR θ (v s ()) () *
        ‖iteratedFDeriv ℝ c (fun x => KPRR x ()) (v s ())‖ₑ
      ≤ ∫⁻ s : Fin 2 → ℝ, 2 * GPRR c * ENNReal.ofReal
          (tri3 θ (X₀ - e₁ * s 0 + e₂ * s 1) (X₁ + e₁ * s 0) (X₂ + e₂ * s 1)) :=
        lintegral_mono fun s => by
          have := enorm_iteratedFDeriv_KPRR_le h0 c (v s ()) ()
          rwa [hv0, hv1, hv2] at this
    _ = 2 * GPRR c * ∫⁻ s : Fin 2 → ℝ, ENNReal.ofReal
          (tri3 θ (X₀ - e₁ * s 0 + e₂ * s 1) (X₁ + e₁ * s 0) (X₂ + e₂ * s 1)) :=
        lintegral_const_mul _ hmT
    _ ≤ 2 * gev (16 * CPhi * CPhi * CPhi) A c * ENNReal.ofReal (D3 θ) :=
        mul_le_mul' (mul_le_mul' le_rfl (GPRR_le c hA)) (lintegral_tri3_le h0 h1 he₁ he₂ X₀ X₁ X₂)
    _ = gev (NPRR θ) A c := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, gev_mul_const _ (by norm_num), mul_comm,
          gev_mul_const _ (D3_nonneg θ)]
        unfold NPRR
        congr 1; ring

end Gamma

section Splits

variable {θ : ℝ} {ε₁ ε₂ : ℤ}

theorem rpow_add5_le (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (a b c d e : ℝ≥0∞) :
    (a + b + c + d + e) ^ θ ≤ a ^ θ + b ^ θ + c ^ θ + d ^ θ + e ^ θ :=
  (rpow_add_le h0 h1 _ _).trans (add_le_add (rpow_add4_le h0 h1 _ _ _ _) le_rfl)

/-- The weight split of the `χ₀` piece of `R R`. -/
theorem wJ_split_RR_M (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {d₁ : ι₁ → ℤ} {d₂ : ι₂ → ℤ} (hd₁ : IsBundle d₁) (hd₂ : IsBundle d₂)
    (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) (γ₁ γ₃ γ₄ γ₆ σ : ℝ) :
    wJ θ α (γ₁ + σ) ≤ 3 * wR θ (vA α) γ₁ γ₃ + 3 * wR θ (vB α) γ₄ γ₆ +
      ((1 + ‖bundle d₁ (vA α) + γ₃ + ε₁ * α (Sum.inr 0)‖ₑ) ^ θ +
        (1 + ‖bundle d₂ (vB α) + γ₆ + ε₂ * α (Sum.inr 1)‖ₑ) ^ θ + (1 + ‖σ‖ₑ)) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set b := ∑ i, ‖vB α i‖ₑ
  set x1 := bundle d₁ (vA α) + γ₃ + ε₁ * α (Sum.inr 0)
  set x2 := bundle d₂ (vB α) + γ₆ + ε₂ * α (Sum.inr 1)
  set W₁ := wR θ (vA α) γ₁ γ₃
  set W₂ := wR θ (vB α) γ₄ γ₆
  have hs1 := special_rpow_le h0 h1 hε₁ (α (Sum.inr 0)) (bundle d₁ (vA α)) γ₃
    (abs_bundle_le hd₁ _)
  have hs2 := special_rpow_le h0 h1 hε₂ (α (Sum.inr 1)) (bundle d₂ (vB α)) γ₆
    (abs_bundle_le hd₂ _)
  have haw : a ^ θ ≤ W₁ := sum_rpow_le_wR h0 _ _ _
  have hgw1 : ‖γ₃‖ₑ ^ θ ≤ W₁ := enorm_rpow_le_wR h0 _ _ _
  have hbw : b ^ θ ≤ W₂ := sum_rpow_le_wR h0 _ _ _
  have hgw2 : ‖γ₆‖ₑ ^ θ ≤ W₂ := enorm_rpow_le_wR h0 _ _ _
  have h1w : (1 + a + ‖γ₁‖ₑ) ^ θ ≤ W₁ := wJ_le_wR h0 _ _ _
  have hx1 : ‖x1‖ₑ ^ θ ≤ (1 + ‖x1‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hx2 : ‖x2‖ₑ ^ θ ≤ (1 + ‖x2‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hL : wJ θ α (γ₁ + σ) = (1 + ∑ j, ‖α j‖ₑ + ‖γ₁ + σ‖ₑ) ^ θ := rfl
  rw [hL, sum_enorm_y4]
  calc (1 + (a + b + ‖α (Sum.inr 0)‖ₑ + ‖α (Sum.inr 1)‖ₑ) + ‖γ₁ + σ‖ₑ) ^ θ
      ≤ ((1 + a + ‖γ₁‖ₑ) + b + ‖α (Sum.inr 0)‖ₑ + ‖α (Sum.inr 1)‖ₑ + ‖σ‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + b + ‖α (Sum.inr 0)‖ₑ + ‖α (Sum.inr 1)‖ₑ) + ‖γ₁ + σ‖ₑ
            ≤ 1 + (a + b + ‖α (Sum.inr 0)‖ₑ + ‖α (Sum.inr 1)‖ₑ) + (‖γ₁‖ₑ + ‖σ‖ₑ) := by
              gcongr; exact enorm_add_le _ _
          _ = _ := by ring
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + b ^ θ + ‖α (Sum.inr 0)‖ₑ ^ θ + ‖α (Sum.inr 1)‖ₑ ^ θ +
          ‖σ‖ₑ ^ θ := rpow_add5_le h0 h1 _ _ _ _ _
    _ ≤ W₁ + W₂ + ((1 + ‖x1‖ₑ) ^ θ + W₁ + W₁) + ((1 + ‖x2‖ₑ) ^ θ + W₂ + W₂) + (1 + ‖σ‖ₑ) :=
        add_le_add (add_le_add (add_le_add (add_le_add h1w hbw)
          (hs1.trans (add_le_add (add_le_add hx1 haw) hgw1)))
          (hs2.trans (add_le_add (add_le_add hx2 hbw) hgw2))) (rpow_le_one_add h0 h1 _)
    _ = _ := by ring

/-- The weight split of the first `χ_∞` piece of `R R` (`γ₁' = γ₁ + γ₂ + γ₄`). -/
theorem wJ_split_RR_P1 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {d₁ ph₁ : ι₁ → ℤ} {d₂ ph₂ : ι₂ → ℤ} (hd₁ : IsBundle d₁)
    (hph₁ : IsBundle ph₁) (hd₂ : IsBundle d₂) (hph₂ : IsBundle ph₂)
    (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) (γ₁ γ₂ γ₃ γ₄ γ₆ : ℝ) :
    wJ θ α (γ₁ + (γ₂ + γ₄)) ≤ 6 * wR θ (vA α) γ₁ γ₃ + 6 * wR θ (vB α) γ₄ γ₆ +
      ((1 + ‖bundle ph₂ (vB α) - bundle ph₁ (vA α) + (γ₂ + γ₄) - ε₁ * α (Sum.inr 0) +
          ε₂ * α (Sum.inr 1)‖ₑ) ^ θ +
        2 * (1 + ‖bundle d₁ (vA α) + γ₃ + ε₁ * α (Sum.inr 0)‖ₑ) ^ θ +
        2 * (1 + ‖bundle d₂ (vB α) + γ₆ + ε₂ * α (Sum.inr 1)‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set b := ∑ i, ‖vB α i‖ₑ
  set f₁ := ‖α (Sum.inr 0)‖ₑ
  set f₂ := ‖α (Sum.inr 1)‖ₑ
  set x0 := bundle ph₂ (vB α) - bundle ph₁ (vA α) + (γ₂ + γ₄) - ε₁ * α (Sum.inr 0) +
    ε₂ * α (Sum.inr 1)
  set x1 := bundle d₁ (vA α) + γ₃ + ε₁ * α (Sum.inr 0)
  set x2 := bundle d₂ (vB α) + γ₆ + ε₂ * α (Sum.inr 1)
  set W₁ := wR θ (vA α) γ₁ γ₃
  set W₂ := wR θ (vB α) γ₄ γ₆
  have hε1 : ‖(ε₁ : ℝ)‖ₑ = 1 := by rcases hε₁ with rfl | rfl <;> simp
  have hε2 : ‖(ε₂ : ℝ)‖ₑ = 1 := by rcases hε₂ with rfl | rfl <;> simp
  have hx : ‖γ₂ + γ₄‖ₑ ≤ ‖x0‖ₑ + b + a + f₁ + f₂ := by
    have : γ₂ + γ₄ = x0 + -bundle ph₂ (vB α) + bundle ph₁ (vA α) + ε₁ * α (Sum.inr 0) +
        -(ε₂ * α (Sum.inr 1)) := by
      simp only [x0]; ring
    rw [this]
    refine (enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans
      (add_le_add ((enorm_add_le _ _).trans (add_le_add ((enorm_add_le _ _).trans
        (add_le_add le_rfl ?_)) ?_)) ?_)) ?_)
    · rw [enorm_neg]; exact abs_bundle_le hph₂ _
    · exact abs_bundle_le hph₁ _
    · rw [enorm_mul, hε1, one_mul]
    · rw [enorm_neg, enorm_mul, hε2, one_mul]
  have hs1 := special_rpow_le h0 h1 hε₁ (α (Sum.inr 0)) (bundle d₁ (vA α)) γ₃
    (abs_bundle_le hd₁ _)
  have hs2 := special_rpow_le h0 h1 hε₂ (α (Sum.inr 1)) (bundle d₂ (vB α)) γ₆
    (abs_bundle_le hd₂ _)
  have haw : a ^ θ ≤ W₁ := sum_rpow_le_wR h0 _ _ _
  have hgw1 : ‖γ₃‖ₑ ^ θ ≤ W₁ := enorm_rpow_le_wR h0 _ _ _
  have hbw : b ^ θ ≤ W₂ := sum_rpow_le_wR h0 _ _ _
  have hgw2 : ‖γ₆‖ₑ ^ θ ≤ W₂ := enorm_rpow_le_wR h0 _ _ _
  have h1w : (1 + a + ‖γ₁‖ₑ) ^ θ ≤ W₁ := wJ_le_wR h0 _ _ _
  have h2 : ∀ u : ℝ≥0∞, (u + u) ^ θ ≤ 2 * u ^ θ := fun u =>
    (rpow_add_le h0 h1 u u).trans_eq (two_mul _).symm
  have hx0 : ‖x0‖ₑ ^ θ ≤ (1 + ‖x0‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hx1 : ‖x1‖ₑ ^ θ ≤ (1 + ‖x1‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hx2 : ‖x2‖ₑ ^ θ ≤ (1 + ‖x2‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hL : wJ θ α (γ₁ + (γ₂ + γ₄)) = (1 + ∑ j, ‖α j‖ₑ + ‖γ₁ + (γ₂ + γ₄)‖ₑ) ^ θ := rfl
  rw [hL, sum_enorm_y4]
  calc (1 + (a + b + f₁ + f₂) + ‖γ₁ + (γ₂ + γ₄)‖ₑ) ^ θ
      ≤ (((1 + a + ‖γ₁‖ₑ) + a) + (b + b) + (f₁ + f₁) + (f₂ + f₂) + ‖x0‖ₑ) ^ θ := by
        refine rpow_mono' h0 ?_
        calc 1 + (a + b + f₁ + f₂) + ‖γ₁ + (γ₂ + γ₄)‖ₑ
            ≤ 1 + (a + b + f₁ + f₂) + (‖γ₁‖ₑ + ‖γ₂ + γ₄‖ₑ) := by
              gcongr; exact enorm_add_le _ _
          _ ≤ 1 + (a + b + f₁ + f₂) + (‖γ₁‖ₑ + (‖x0‖ₑ + b + a + f₁ + f₂)) := by gcongr
          _ = _ := by ring
    _ ≤ ((1 + a + ‖γ₁‖ₑ) + a) ^ θ + (b + b) ^ θ + (f₁ + f₁) ^ θ + (f₂ + f₂) ^ θ + ‖x0‖ₑ ^ θ :=
        rpow_add5_le h0 h1 _ _ _ _ _
    _ ≤ ((1 + a + ‖γ₁‖ₑ) ^ θ + a ^ θ) + 2 * b ^ θ + 2 * f₁ ^ θ + 2 * f₂ ^ θ + ‖x0‖ₑ ^ θ :=
        add_le_add (add_le_add (add_le_add (add_le_add (rpow_add_le h0 h1 _ _) (h2 b)) (h2 f₁))
          (h2 f₂)) le_rfl
    _ ≤ (W₁ + W₁) + 2 * W₂ + 2 * ((1 + ‖x1‖ₑ) ^ θ + W₁ + W₁) +
          2 * ((1 + ‖x2‖ₑ) ^ θ + W₂ + W₂) + (1 + ‖x0‖ₑ) ^ θ := by
        gcongr
        · exact hs1.trans (add_le_add (add_le_add hx1 haw) hgw1)
        · exact hs2.trans (add_le_add (add_le_add hx2 hbw) hgw2)
    _ ≤ (W₁ + W₁) + 2 * W₂ + 2 * ((1 + ‖x1‖ₑ) ^ θ + W₁ + W₁) +
          2 * ((1 + ‖x2‖ₑ) ^ θ + W₂ + W₂) + ((1 + ‖x0‖ₑ) ^ θ + 1) := by gcongr; exact le_self_add
    _ = _ := by ring

/-- The weight split of the second `χ_∞` piece of `R R` (`γ₁' = γ₁`). -/
theorem wJ_split_RR_P2 (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hε₁ : ε₁ = 1 ∨ ε₁ = -1)
    (hε₂ : ε₂ = 1 ∨ ε₂ = -1) {d₁ : ι₁ → ℤ} {d₂ : ι₂ → ℤ} (hd₁ : IsBundle d₁) (hd₂ : IsBundle d₂)
    (α : (ι₁ ⊕ ι₂) ⊕ Fin 2 → ℝ) (γ₁ γ₃ γ₄ γ₆ x0 : ℝ) :
    wJ θ α γ₁ ≤ 3 * wR θ (vA α) γ₁ γ₃ + 3 * wR θ (vB α) γ₄ γ₆ +
      ((1 + ‖x0‖ₑ) ^ θ + 2 * (1 + ‖bundle d₁ (vA α) + γ₃ + ε₁ * α (Sum.inr 0)‖ₑ) ^ θ +
        2 * (1 + ‖bundle d₂ (vB α) + γ₆ + ε₂ * α (Sum.inr 1)‖ₑ) ^ θ + 1) := by
  set a := ∑ i, ‖vA α i‖ₑ
  set b := ∑ i, ‖vB α i‖ₑ
  set x1 := bundle d₁ (vA α) + γ₃ + ε₁ * α (Sum.inr 0)
  set x2 := bundle d₂ (vB α) + γ₆ + ε₂ * α (Sum.inr 1)
  set W₁ := wR θ (vA α) γ₁ γ₃
  set W₂ := wR θ (vB α) γ₄ γ₆
  have hs1 := special_rpow_le h0 h1 hε₁ (α (Sum.inr 0)) (bundle d₁ (vA α)) γ₃
    (abs_bundle_le hd₁ _)
  have hs2 := special_rpow_le h0 h1 hε₂ (α (Sum.inr 1)) (bundle d₂ (vB α)) γ₆
    (abs_bundle_le hd₂ _)
  have haw : a ^ θ ≤ W₁ := sum_rpow_le_wR h0 _ _ _
  have hgw1 : ‖γ₃‖ₑ ^ θ ≤ W₁ := enorm_rpow_le_wR h0 _ _ _
  have hbw : b ^ θ ≤ W₂ := sum_rpow_le_wR h0 _ _ _
  have hgw2 : ‖γ₆‖ₑ ^ θ ≤ W₂ := enorm_rpow_le_wR h0 _ _ _
  have h1w : (1 + a + ‖γ₁‖ₑ) ^ θ ≤ W₁ := wJ_le_wR h0 _ _ _
  have hx1 : ‖x1‖ₑ ^ θ ≤ (1 + ‖x1‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hx2 : ‖x2‖ₑ ^ θ ≤ (1 + ‖x2‖ₑ) ^ θ := rpow_mono' h0 le_add_self
  have hL : wJ θ α γ₁ = (1 + ∑ j, ‖α j‖ₑ + ‖γ₁‖ₑ) ^ θ := rfl
  rw [hL, sum_enorm_y4]
  calc (1 + (a + b + ‖α (Sum.inr 0)‖ₑ + ‖α (Sum.inr 1)‖ₑ) + ‖γ₁‖ₑ) ^ θ
      = ((1 + a + ‖γ₁‖ₑ) + b + ‖α (Sum.inr 0)‖ₑ + ‖α (Sum.inr 1)‖ₑ) ^ θ := by ring_nf
    _ ≤ (1 + a + ‖γ₁‖ₑ) ^ θ + b ^ θ + ‖α (Sum.inr 0)‖ₑ ^ θ + ‖α (Sum.inr 1)‖ₑ ^ θ :=
        rpow_add4_le h0 h1 _ _ _ _
    _ ≤ W₁ + W₂ + ((1 + ‖x1‖ₑ) ^ θ + W₁ + W₁) + ((1 + ‖x2‖ₑ) ^ θ + W₂ + W₂) :=
        add_le_add (add_le_add (add_le_add h1w hbw)
          (hs1.trans (add_le_add (add_le_add hx1 haw) hgw1)))
          (hs2.trans (add_le_add (add_le_add hx2 hbw) hgw2))
    _ ≤ W₁ + W₂ + ((1 + ‖x1‖ₑ) ^ θ + W₁ + W₁) + ((1 + ‖x2‖ₑ) ^ θ + W₂ + W₂) +
          ((1 + ‖x0‖ₑ) ^ θ + (1 + ‖x1‖ₑ) ^ θ + (1 + ‖x2‖ₑ) ^ θ + 1) := le_self_add
    _ = _ := by ring

end Splits

end WaveTurbulence.ClassJR
