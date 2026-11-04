/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChainX
public import WaveTurbulence.Foundations.ClassJR.MCPair
public import WaveTurbulence.Foundations.ClassJR.MCDiff

/-!
# The symbols of the pairs of a chain

In Case 2 of DH21 Proposition 5.1, after fixing the frequencies, the coefficient of the chain integral
is the product over the pairs `j` of the pair symbols `𝒞_j(α_j, λ_j)`, times, for the pairs `j` moved
from `Z⁺` to `W⁺` (DH21 L1141–L1145), the difference `Φ(ε_jα_j + λ_{j,1}) - Φ(ε_jα_j)`. We attach the
difference to the pair symbol (`pdC`). Then every pair symbol satisfies the interface `PBound`:
Gevrey bounds, per-variable weighted bounds, and a frequency-weighted bound, with no `θ` weight.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section PSym

/-- **A pair symbol** on its own variables. -/
structure PSym (V : Type) where
  /-- The index type of the variables. -/
  ι : Type
  [fin : Fintype ι]
  /-- The variables. -/
  f : ι → V
  /-- The symbol. -/
  C : (ι → ℝ) → ℝ × ℝ → ℂ

attribute [instance] PSym.fin

variable {V : Type}

/-- **The bounds of a pair symbol** used in the assembly. -/
structure PBound (A N b : ℝ) (P : PSym V) : Prop where
  nonneg : 0 ≤ N
  smooth : ∀ z, ContDiff ℝ ∞ fun β => P.C β z
  meas : StronglyMeasurable (Function.uncurry P.C)
  norm : ∀ k, ∫⁻ β, ∫⁻ z, dnorm k P.C β z ≤ gev N A k
  wvar : ∀ i, ∫⁻ β, ∫⁻ z, (1 + ‖β i‖ₑ) ^ b * dnorm 0 P.C β z ≤ ENNReal.ofReal N
  wfreq : ∫⁻ β, ∫⁻ z, (1 + ‖z.1‖ₑ) ^ b * dnorm 0 P.C β z ≤ ENNReal.ofReal N

theorem PBound.mono {A N N' b : ℝ} {P : PSym V} (h : PBound A N b P) (hN : N ≤ N') (hA : 0 ≤ A) :
    PBound A N' b P where
  nonneg := h.nonneg.trans hN
  smooth := h.smooth
  meas := h.meas
  norm k := (h.norm k).trans (gev_mono hN hA le_rfl (h.nonneg.trans hN) k)
  wvar i := (h.wvar i).trans (ENNReal.ofReal_le_ofReal hN)
  wfreq := h.wfreq.trans (ENNReal.ofReal_le_ofReal hN)

theorem PBound.of_srep {θ a b A N : ℝ} {ι : Type} [Fintype ι] {f : ι → V}
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (h : SRep θ a b A N C) (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbθ : b ≤ θ) : PBound A N b ⟨ι, f, C⟩ where
  nonneg := h.nonneg
  smooth := h.reg.smooth
  meas := h.reg.meas
  norm k := h.norm_unweighted hθ k
  wvar i := h.var_le ha i
  wfreq := by
    refine le_trans (lintegral_mono fun β => lintegral_mono fun z =>
      mul_le_mul' (one_add_rpow_le_wL hb hbθ z) le_rfl) ((h.norm 0).trans_eq (gev_zero_eq N A))

end PSym

section PD

/-- The coupling of the difference `Φ(εx + λ₁) - Φ(εx)` (one variable `x`). -/
@[expose] noncomputable def dK (ε : ℤ) (x : Unit → ℝ) (p : (ℝ × ℝ) × Unit) : ℂ :=
  Dfun ε p.1.1 (x ())

variable {ι : Type} [Fintype ι]

/-- **The pair symbol with the difference**: `𝒞(β, λ) (Φ(εx + λ₁) - Φ(εx))`. -/
@[expose] noncomputable def pdC (C : (ι → ℝ) → ℝ × ℝ → ℂ) (ε : ℤ) : (ι ⊕ Unit → ℝ) → ℝ × ℝ → ℂ :=
  fun α z => kprod C (dK ε) α (z, ())

theorem contDiff_dK (ε : ℤ) (p : (ℝ × ℝ) × Unit) : ContDiff ℝ ∞ fun x => dK ε x p := by
  unfold dK
  exact (contDiff_Dfun ε p.1.1).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℝ) ()).contDiff

theorem measurable_dK (ε : ℤ) : StronglyMeasurable (Function.uncurry (dK ε)) := by
  have : Function.uncurry (dK ε) = (fun q : ℝ × ℝ => Dfun ε q.1 q.2) ∘
      (fun x : (Unit → ℝ) × ((ℝ × ℝ) × Unit) => (x.2.1.1, x.1 ())) := rfl
  rw [this]
  exact ((measurable_Dfun ε).comp (by fun_prop)).stronglyMeasurable

theorem dnorm_dK_le (ε : ℤ) (j : ℕ) (x : Unit → ℝ) (p : (ℝ × ℝ) × Unit) :
    dnorm j (dK ε) x p ≤ ‖iteratedDeriv j (Dfun ε p.1.1) (x ())‖ₑ := by
  have h := dnorm_comp_bundle_le (y := fun _ : Unit => (1 : ℤ)) isBundle_one
    (F := fun u (q : (ℝ × ℝ) × Unit) => Dfun ε q.1.1 u)
    (fun q => contDiff_Dfun ε q.1.1) j x p
  have e : dK ε = fun (x : Unit → ℝ) (p : (ℝ × ℝ) × Unit) =>
      Dfun ε p.1.1 (bundle (fun _ : Unit => (1 : ℤ)) x) := by
    funext x p; simp [dK, bundle_one]
  rw [e]
  rw [bundle_one] at h
  exact h

theorem lintegral_prod_punit {X : Type*} [MeasureSpace X] [SFinite (volume : Measure X)]
    {F : X × Unit → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p = ∫⁻ x, F (x, ()) := by
  rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
  congr 1
  funext x
  rw [show (volume : Measure Unit) = Measure.dirac () from rfl, lintegral_dirac]

/-- The coupling bound of the difference for a weight on its variable. -/
theorem lintegral_dK_le {g : ℕ → ℝ≥0∞} {v : ℝ × ℝ → ℝ≥0∞} {w : ℝ → ℝ≥0∞} {ε : ℤ}
    (hgv : ∀ j (z : ℝ × ℝ), ∫⁻ t : ℝ, w t * ‖iteratedDeriv j (Dfun ε z.1) t‖ₑ ≤ g j * v z) :
    ∀ j (z : ℝ × ℝ), ∫⁻ x : Unit → ℝ, ∫⁻ q : Unit, w (x ()) * dnorm j (dK ε) x (z, q) ≤
      g j * v z := by
  intro j z
  calc ∫⁻ x : Unit → ℝ, ∫⁻ q : Unit, w (x ()) * dnorm j (dK ε) x (z, q)
      ≤ ∫⁻ x : Unit → ℝ, w (x ()) * ‖iteratedDeriv j (Dfun ε z.1) (x ())‖ₑ := by
        refine lintegral_mono fun x => ?_
        rw [show (volume : Measure Unit) = Measure.dirac () from rfl, lintegral_dirac]
        exact mul_le_mul' le_rfl (dnorm_dK_le ε j x (z, ()))
    _ = ∫⁻ t : ℝ, w t * ‖iteratedDeriv j (Dfun ε z.1) t‖ₑ :=
        lintegral_unitFun (G := fun t => w t * ‖iteratedDeriv j (Dfun ε z.1) t‖ₑ)
    _ ≤ g j * v z := hgv j z

end PD

section PDBound

variable {ι : Type} [Fintype ι]

theorem dnorm_pdC (C : (ι → ℝ) → ℝ × ℝ → ℂ) (ε : ℤ) (k : ℕ) (α : ι ⊕ Unit → ℝ) (z : ℝ × ℝ) :
    dnorm k (pdC C ε) α z = dnorm k (kprod C (dK ε)) α (z, ()) := rfl

theorem contDiff_pdC {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : ∀ z, ContDiff ℝ ∞ fun β => C β z) (ε : ℤ)
    (z : ℝ × ℝ) : ContDiff ℝ ∞ fun α => pdC C ε α z :=
  contDiff_kprod hC (contDiff_dK ε) (z, ())

omit [Fintype ι] in
theorem measurable_pdC {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : StronglyMeasurable (Function.uncurry C))
    (ε : ℤ) : StronglyMeasurable (Function.uncurry (pdC C ε)) := by
  have h := measurable_kprod hC (measurable_dK ε)
  have : Function.uncurry (pdC C ε) = Function.uncurry (kprod C (dK ε)) ∘
      (fun x : (ι ⊕ Unit → ℝ) × (ℝ × ℝ) => (x.1, (x.2, ()))) := rfl
  rw [this]
  exact (h.measurable.comp (by fun_prop)).stronglyMeasurable

/-- **Weighted norms of the pair symbol with the difference** (DH21 L1141–L1145 with Lemma A.4). -/
theorem lintegral_pdC_le {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hCs : ∀ z, ContDiff ℝ ∞ fun β => C β z)
    (hCm : StronglyMeasurable (Function.uncurry C)) {ε : ℤ}
    {wM : (ι → ℝ) → ℝ × ℝ → ℝ≥0∞} (hwM : Measurable (Function.uncurry wM))
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) {v : ℝ × ℝ → ℝ≥0∞} (hv : Measurable v) {g : ℕ → ℝ≥0∞}
    (hgv : ∀ j (z : ℝ × ℝ), ∫⁻ t : ℝ, w t * ‖iteratedDeriv j (Dfun ε z.1) t‖ₑ ≤ g j * v z)
    (k : ℕ) :
    ∫⁻ α : ι ⊕ Unit → ℝ, ∫⁻ z, wM (fun i => α (Sum.inl i)) z * w (α (Sum.inr ())) *
        dnorm k (pdC C ε) α z ≤
      ∑ j ∈ range (k + 1), (k.choose j : ℝ≥0∞) *
        (∫⁻ α₁, ∫⁻ z, wM α₁ z * v z * dnorm j C α₁ z) * g (k - j) := by
  have hwK : Measurable (Function.uncurry fun (x : Unit → ℝ) (_ : (ℝ × ℝ) × Unit) => w (x ())) := by
    change Measurable fun x : (Unit → ℝ) × ((ℝ × ℝ) × Unit) => w (x.1 ())
    fun_prop
  have h := lintegral_kprod_le hCs hCm (contDiff_dK ε) (measurable_dK ε) hwM hwK hv
    (lintegral_dK_le hgv) k
  refine le_trans (le_of_eq ?_) h
  refine lintegral_congr fun α => ?_
  simp only [dnorm_pdC]
  have hm := measurable_dnorm (contDiff_kprod (Q := Unit) hCs (contDiff_dK ε))
    (measurable_kprod hCm (measurable_dK ε)) k
  have h1 : Measurable fun p : (ℝ × ℝ) × Unit => wM (fun i => α (Sum.inl i)) p.1 :=
    hwM.comp (measurable_const.prodMk measurable_fst)
  have h3 : Measurable fun p : (ℝ × ℝ) × Unit => dnorm k (kprod C (dK ε)) α p :=
    hm.of_uncurry_left
  have h2 : Measurable fun _ : (ℝ × ℝ) × Unit => w (α (Sum.inr ())) := measurable_const
  exact (lintegral_prod_punit ((h1.mul h2).mul h3)).symm

/-- The `k = 0` case of `lintegral_pdC_le`. -/
theorem lintegral_pdC_zero_le {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hCs : ∀ z, ContDiff ℝ ∞ fun β => C β z)
    (hCm : StronglyMeasurable (Function.uncurry C)) {ε : ℤ}
    {wM : (ι → ℝ) → ℝ × ℝ → ℝ≥0∞} (hwM : Measurable (Function.uncurry wM))
    {w : ℝ → ℝ≥0∞} (hw : Measurable w) {v : ℝ × ℝ → ℝ≥0∞} (hv : Measurable v) (hv1 : ∀ z, 1 ≤ v z)
    {c : ℝ≥0∞} (hgv : ∀ z : ℝ × ℝ, ∫⁻ t : ℝ, w t * ‖Dfun ε z.1 t‖ₑ ≤ c * v z) :
    ∫⁻ α : ι ⊕ Unit → ℝ, ∫⁻ z, wM (fun i => α (Sum.inl i)) z * w (α (Sum.inr ())) *
        dnorm 0 (pdC C ε) α z ≤ (∫⁻ α₁, ∫⁻ z, wM α₁ z * v z * ‖C α₁ z‖ₑ) * c := by
  have h := lintegral_pdC_le hCs hCm (ε := ε) hwM hw hv (g := fun j => if j = 0 then c else ⊤) ?_ 0
  · simpa [dnorm_zero] using h
  · intro j z
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simpa using hgv z
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hj.ne'), ENNReal.top_mul (ne_of_gt (lt_of_lt_of_le one_pos (hv1 z)))]
      exact le_top

/-- The constant of the pair symbol with the difference. -/
@[expose] noncomputable def KPD (a b : ℝ) : ℝ := 4 * (CDg a + CD b a)

theorem KPD_nonneg (a b : ℝ) : 0 ≤ KPD a b := by
  have := CDg_nonneg a; have := CD_nonneg b a
  unfold KPD; positivity

end PDBound

section PDPair

variable {V : Type}

/-- **The pair with the difference** (DH21 L1141–L1145): the variables of the pair together with the
variable `x₀ = α_j` of `Φ(ε_jα_j + λ_{j,1}) - Φ(ε_jα_j)`. -/
@[expose] noncomputable def PSym.pd (P : PSym V) (x₀ : V) (ε : ℤ) : PSym V :=
  ⟨P.ι ⊕ Unit, Sum.elim P.f fun _ => x₀, pdC P.C ε⟩

theorem KPD_bounds {a b N : ℝ} (hN : 0 ≤ N) :
    N * CDg a ≤ KPD a b * N ∧ N * CD b a ≤ KPD a b * N ∧ 4 * N * CDg a ≤ KPD a b * N := by
  have h1 := mul_nonneg (CDg_nonneg a) hN
  have h2 := mul_nonneg (CD_nonneg b a) hN
  unfold KPD
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- **The bounds of the pair symbol with the difference**, from the coefficient bounds of the pair
(DH21 L1141–L1145; the logarithmic loss of the difference is `⟨λ_{j,1}⟩^a`, paid by the `θ`-weight
of the pair since `a + b ≤ θ`). -/
theorem PBound.pd {θ a b A N : ℝ} {P : PSym V} (h : SRep θ a b A N P.C) (ha : 0 < a) (hb : 0 ≤ b)
    (hab : a + b ≤ θ) (hθ1 : θ ≤ 1) (hA : Achi ≤ A) (x₀ : V) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    PBound A (KPD a b * N) b (P.pd x₀ ε) := by
  have ha1 : a ≤ 1 := by linarith
  have haθ : a ≤ θ := by linarith
  have hA0 : 0 ≤ A := Achi_nonneg.trans hA
  obtain ⟨hK1, hK2, hK3⟩ := KPD_bounds (a := a) (b := b) h.nonneg
  have hv : ∀ c : ℝ, Measurable fun z : ℝ × ℝ => ((1 : ℝ≥0∞) + ‖z.1‖ₑ) ^ c := fun c => by
    fun_prop
  have hv1 : ∀ {c : ℝ}, 0 < c → ∀ z : ℝ × ℝ, 1 ≤ ((1 : ℝ≥0∞) + ‖z.1‖ₑ) ^ c := fun hc _ =>
    ENNReal.one_le_rpow le_self_add hc
  have hg0 : ∀ z : ℝ × ℝ, ∫⁻ t : ℝ, (fun _ => (1 : ℝ≥0∞)) t * ‖Dfun ε z.1 t‖ₑ ≤
      ENNReal.ofReal (CDg a) * ((1 : ℝ≥0∞) + ‖z.1‖ₑ) ^ a := fun z => by
    simpa [gev_zero_eq] using lintegral_Dfun_gev_le ha ha1 hε z.1 0
  have hwθ : ∀ {c : ℝ}, 0 ≤ c → c ≤ θ → ∀ β : P.ι → ℝ,
      ∫⁻ z, ((1 : ℝ≥0∞) + ‖z.1‖ₑ) ^ c * ‖P.C β z‖ₑ ≤ ∫⁻ z, wL θ z * dnorm 0 P.C β z :=
    fun hc hcθ β => lintegral_mono fun z => by
      rw [dnorm_zero]; exact mul_le_mul' (one_add_rpow_le_wL hc hcθ z) le_rfl
  have hN0 : ∀ {c : ℝ}, 0 ≤ c → c ≤ θ →
      ∫⁻ β, ∫⁻ z, ((1 : ℝ≥0∞) + ‖z.1‖ₑ) ^ c * ‖P.C β z‖ₑ ≤ ENNReal.ofReal N := fun hc hcθ =>
    (lintegral_mono fun β => hwθ hc hcθ β).trans ((h.norm 0).trans_eq (gev_zero_eq N A))
  refine ⟨mul_nonneg (KPD_nonneg a b) h.nonneg, fun z => contDiff_pdC h.reg.smooth ε z,
    measurable_pdC h.reg.meas ε, ?_, ?_, ?_⟩
  · -- the Gevrey bounds
    intro k
    show ∫⁻ β : P.ι ⊕ Unit → ℝ, ∫⁻ z, dnorm k (pdC P.C ε) β z ≤ gev (KPD a b * N) A k
    have h1 := lintegral_pdC_le h.reg.smooth h.reg.meas (ε := ε) (wM := fun _ _ => 1)
      measurable_const (w := fun _ => 1) measurable_const (hv a) (g := gev (CDg a) Achi)
      (fun j z => by simpa using lintegral_Dfun_gev_le ha ha1 hε z.1 j) k
    simp only [one_mul] at h1
    refine h1.trans ((gev_conv_le h.nonneg (CDg_nonneg a) hA0 (fun j => ?_)
      (fun j => gev_mono le_rfl Achi_nonneg hA (CDg_nonneg a) j) k).trans
      (gev_mono hK3 hA0 le_rfl (mul_nonneg (KPD_nonneg a b) h.nonneg) k))
    exact le_trans (lintegral_mono fun β => lintegral_mono fun z =>
      mul_le_mul' (one_add_rpow_le_wL ha.le haθ z) le_rfl) (h.norm j)
  · -- the per-variable bounds
    rintro (i | u)
    · show ∫⁻ β : P.ι ⊕ Unit → ℝ, ∫⁻ z, (1 + ‖β (Sum.inl i)‖ₑ) ^ b *
          dnorm 0 (pdC P.C ε) β z ≤ ENNReal.ofReal (KPD a b * N)
      have hw : Measurable (Function.uncurry fun (β : P.ι → ℝ) (_ : ℝ × ℝ) =>
          ((1 : ℝ≥0∞) + ‖β i‖ₑ) ^ b) := by
        change Measurable fun x : (P.ι → ℝ) × (ℝ × ℝ) => ((1 : ℝ≥0∞) + ‖x.1 i‖ₑ) ^ b
        fun_prop
      have h1 := lintegral_pdC_zero_le h.reg.smooth h.reg.meas (ε := ε) hw (w := fun _ => 1)
        measurable_const (hv a) (hv1 ha) hg0
      simp only [mul_one] at h1
      refine h1.trans ?_
      calc (∫⁻ α₁, ∫⁻ z, (1 + ‖α₁ i‖ₑ) ^ b * (1 + ‖z.1‖ₑ) ^ a * ‖P.C α₁ z‖ₑ) *
            ENNReal.ofReal (CDg a) ≤ ENNReal.ofReal N * ENNReal.ofReal (CDg a) := by
            gcongr
            refine le_trans (lintegral_mono fun β => lintegral_mono fun z => ?_) (h.wnorm i)
            rw [mul_comm (((1 : ℝ≥0∞) + ‖β i‖ₑ) ^ b)]
            gcongr
            exact one_add_rpow_le_wL ha.le le_rfl z
        _ ≤ ENNReal.ofReal (KPD a b * N) := by
            rw [← ENNReal.ofReal_mul h.nonneg]; exact ENNReal.ofReal_le_ofReal hK1
    · obtain ⟨⟩ := u
      show ∫⁻ β : P.ι ⊕ Unit → ℝ, ∫⁻ z, (1 + ‖β (Sum.inr ())‖ₑ) ^ b *
          dnorm 0 (pdC P.C ε) β z ≤ ENNReal.ofReal (KPD a b * N)
      have h1 := lintegral_pdC_zero_le h.reg.smooth h.reg.meas (ε := ε) (wM := fun _ _ => 1)
        measurable_const (w := fun t => ((1 : ℝ≥0∞) + ‖t‖ₑ) ^ b) (by fun_prop) (hv (b + a))
        (hv1 (by linarith)) (c := ENNReal.ofReal (CD b a)) (fun z =>
          (lintegral_weight_Dfun_le hb ha (by linarith) hε z.1).trans_eq
            (by rw [ENNReal.ofReal_mul (CD_nonneg b a), one_add_enorm_rpow_eq]))
      simp only [one_mul] at h1
      refine h1.trans ?_
      calc (∫⁻ α₁, ∫⁻ z, (1 + ‖z.1‖ₑ) ^ (b + a) * ‖P.C α₁ z‖ₑ) * ENNReal.ofReal (CD b a)
          ≤ ENNReal.ofReal N * ENNReal.ofReal (CD b a) := by
            gcongr
            exact hN0 (by linarith) (by linarith)
        _ ≤ ENNReal.ofReal (KPD a b * N) := by
            rw [← ENNReal.ofReal_mul h.nonneg]; exact ENNReal.ofReal_le_ofReal hK2
  · -- the frequency-weighted bound
    show ∫⁻ β : P.ι ⊕ Unit → ℝ, ∫⁻ z, (1 + ‖z.1‖ₑ) ^ b * dnorm 0 (pdC P.C ε) β z ≤
      ENNReal.ofReal (KPD a b * N)
    have hw : Measurable (Function.uncurry fun (_ : P.ι → ℝ) (z : ℝ × ℝ) =>
        ((1 : ℝ≥0∞) + ‖z.1‖ₑ) ^ b) := by
      change Measurable fun x : (P.ι → ℝ) × (ℝ × ℝ) => ((1 : ℝ≥0∞) + ‖x.2.1‖ₑ) ^ b
      fun_prop
    have h1 := lintegral_pdC_zero_le h.reg.smooth h.reg.meas (ε := ε) hw (w := fun _ => 1)
      measurable_const (hv a) (hv1 ha) hg0
    simp only [mul_one] at h1
    refine h1.trans ?_
    calc (∫⁻ α₁, ∫⁻ z, (1 + ‖z.1‖ₑ) ^ b * (1 + ‖z.1‖ₑ) ^ a * ‖P.C α₁ z‖ₑ) *
          ENNReal.ofReal (CDg a) ≤ ENNReal.ofReal N * ENNReal.ofReal (CDg a) := by
          gcongr
          refine le_trans (lintegral_mono fun β => lintegral_mono fun z => le_of_eq ?_)
            (hN0 (c := b + a) (by linarith) (by linarith))
          rw [ENNReal.rpow_add _ _ (ne_of_gt (lt_of_lt_of_le one_pos le_self_add))
            (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, enorm_ne_top⟩)]
      _ ≤ ENNReal.ofReal (KPD a b * N) := by
          rw [← ENNReal.ofReal_mul h.nonneg]; exact ENNReal.ofReal_le_ofReal hK1

end PDPair

end WaveTurbulence.ClassJR
