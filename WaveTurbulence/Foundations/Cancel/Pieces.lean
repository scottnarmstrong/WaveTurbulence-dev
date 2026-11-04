/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.Kernels

/-!
# The regularized pair pieces and sandwiches (DH21 Lemmas 7.1, 7.3)

The variable `α_j` of a pair of a regular chain enters DH21 Lemma 5.10's operators in two shapes:

* an adjacent pair `{a, a+1}` gives `I_{εα} I_{μ-εα} = Φ(εα) 𝒥_{α[ ],μ} + (𝒥_{α,μ} + ℛ_{α,μ})` (DH21 Lemma 5.8),
  with `𝒥_{α[ ],μ} = -I_μ`. Its `α`-dependent part is `tr58K ε μ x = I_{εx}I_{μ-εx} + Φ(εx) I_μ`
  (`ClassJR.TR58`).
* a non-adjacent pair encloses an operator `T` in a sandwich `I_{εα} T I_{μ-εα}` (`ClassJR.sandw`).

Regularizing in `x = α`:

* `greg_tr58K`: `greg θ (x ↦ tr58K ε μ x t s) = e^{πiμs} GI θ (t-s)` with `GI θ u = ∫_0^u gk θ → 1`. So
  `[G]∫ (𝒥 + ℛ) dα = I_μ` (DH21 Lemma 7.3; `Φ` is odd and drops out).
* `greg_sandK`: the sandwich regularizes to `e^{πiμs} ∫_s^t gk θ(y-s) H(y,s) dy` with
  `H(y,s) = ∫_s^y T(y,z) dz`, which tends to `H(s,s) = 0` (`tendsto_greg_sandK`; DH21 Lemma 7.1).

`kcomp_assoc` (associativity of Volterra kernel composition) writes the sandwich in the right-associated form.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR WaveTurbulence.Fourier

/-! ### Associativity -/

/-- Cutting an interval integral at an interior point with a step function. -/
theorem integral_ite_le_left {f : ℝ → ℂ} (hf : Continuous f) {s z t : ℝ} (hz : z ∈ Icc s t) :
    (∫ y in s..t, if z ≤ y then f y else 0) = ∫ y in z..t, f y := by
  have hnull : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ z :=
    (measure_eq_zero_iff_ae_notMem.1 (measure_singleton z)).mono fun y hy => hy
  have h1 : IntervalIntegrable (fun y => if z ≤ y then f y else 0) volume s z := by
    refine (intervalIntegrable_const (c := (0 : ℂ))).congr_uIoo fun y hy => ?_
    rw [uIoo_of_le hz.1] at hy
    simp [not_le.2 hy.2]
  have h2 : IntervalIntegrable (fun y => if z ≤ y then f y else 0) volume z t := by
    refine (hf.intervalIntegrable z t).congr_uIoo fun y hy => ?_
    rw [uIoo_of_le hz.2] at hy
    simp [hy.1.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : (∫ y in s..z, if z ≤ y then f y else 0) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℂ)) ?_]
    · simp
    filter_upwards [hnull] with y hyz hy
    rw [uIoc_of_le hz.1] at hy
    simp [not_le.2 (lt_of_le_of_ne hy.2 hyz)]
  have e2 : (∫ y in z..t, if z ≤ y then f y else 0) = ∫ y in z..t, f y := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hz.2] at hy
    simp [hy.1]
  rw [e1, e2, zero_add]

theorem integral_ite_le_right {f : ℝ → ℂ} (hf : Continuous f) {s y t : ℝ} (hy : y ∈ Icc s t) :
    (∫ z in s..t, if z ≤ y then f z else 0) = ∫ z in s..y, f z := by
  have hnull : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ y :=
    (measure_eq_zero_iff_ae_notMem.1 (measure_singleton y)).mono fun z hz => hz
  have h1 : IntervalIntegrable (fun z => if z ≤ y then f z else 0) volume s y := by
    refine (hf.intervalIntegrable s y).congr_uIoo fun z hz => ?_
    rw [uIoo_of_le hy.1] at hz
    simp [hz.2.le]
  have h2 : IntervalIntegrable (fun z => if z ≤ y then f z else 0) volume y t := by
    refine (intervalIntegrable_const (c := (0 : ℂ))).congr_uIoo fun z hz => ?_
    rw [uIoo_of_le hy.2] at hz
    simp [not_le.2 hz.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have e1 : (∫ z in s..y, if z ≤ y then f z else 0) = ∫ z in s..y, f z := by
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [uIcc_of_le hy.1] at hz
    simp [hz.2]
  have e2 : (∫ z in y..t, if z ≤ y then f z else 0) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℂ)) ?_]
    · simp
    filter_upwards [hnull] with z hzy hz
    rw [uIoc_of_le hy.2] at hz
    simp [not_le.2 hz.1]
  rw [e1, e2, add_zero]

/-- **Associativity of the composition of continuous Volterra kernels** (on `s ≤ t`). -/
theorem kcomp_assoc {A K B : ℝ → ℝ → ℂ} (hA : KCont A) (hK : KCont K) (hB : KCont B) {t s : ℝ}
    (hst : s ≤ t) : kcomp (kcomp A K) B t s = kcomp A (kcomp K B) t s := by
  set f : ℝ → ℝ → ℂ := fun z y => A t y * K y z * B z s with hf
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hf]
    exact ((hA.comp (continuous_const.prodMk continuous_snd)).mul
      (hK.comp (continuous_snd.prodMk continuous_fst))).mul
      (hB.comp (continuous_fst.prodMk continuous_const))
  set F : ℝ → ℝ → ℂ := fun z y => if z ≤ y then f z y else 0 with hF
  have hFm : Measurable (Function.uncurry F) := by
    have : Function.uncurry F = fun p : ℝ × ℝ => if p.1 ≤ p.2 then Function.uncurry f p else 0 := by
      funext p; rfl
    rw [this]
    exact Measurable.ite (measurableSet_le measurable_fst measurable_snd) hfc.measurable
      measurable_const
  have hL : kcomp (kcomp A K) B t s = ∫ z in s..t, ∫ y in s..t, F z y := by
    unfold kcomp
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [uIcc_of_le hst] at hz
    simp only [hF]
    rw [integral_ite_le_left (f := f z) (hfc.comp (continuous_const.prodMk continuous_id)) hz,
      ← intervalIntegral.integral_mul_const]
  have hR : kcomp A (kcomp K B) t s = ∫ y in s..t, ∫ z in s..t, F z y := by
    unfold kcomp
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hst] at hy
    simp only [hF]
    rw [integral_ite_le_right (f := fun z => f z y) (hfc.comp (continuous_id.prodMk continuous_const)) hy,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun z _ => ?_
    simp only [hf]; ring
  rw [hL, hR]
  refine intervalIntegral_intervalIntegral_swap ?_
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_Icc (a := s) (b := t))).exists_bound_of_continuousOn
    (hfc.continuousOn (s := Icc s t ×ˢ Icc s t))
  refine Measure.integrableOn_of_bounded (M := max M 0) ?_ hFm.aestronglyMeasurable ?_
  · exact ((measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)).trans_lt
      ((isCompact_uIcc.prod isCompact_uIcc).measure_lt_top)).ne
  · rw [ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_uIoc)]
    refine Eventually.of_forall fun p hp => ?_
    have h1 : p.1 ∈ Icc s t := by rw [← uIcc_of_le hst]; exact uIoc_subset_uIcc hp.1
    have h2 : p.2 ∈ Icc s t := by rw [← uIcc_of_le hst]; exact uIoc_subset_uIcc hp.2
    simp only [Function.uncurry, hF]
    split_ifs
    · exact (hM (p.1, p.2) ⟨h1, h2⟩).trans (le_max_left _ _)
    · simp

/-! ### Elementary kernels -/

theorem norm_cexp_piI (r : ℝ) : ‖cexp (π * I * r)‖ = 1 := by
  rw [show (π : ℂ) * I * r = ((π * r : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem norm_iker (β t s : ℝ) : ‖iker β t s‖ = 1 := by
  unfold iker; exact_mod_cast norm_cexp_piI (β * s)

theorem kcont_iker (β : ℝ) : KCont (iker β) := continuous_iker β

/-- The constant kernel `1`. -/
@[expose] def one : ℝ → ℝ → ℂ := fun _ _ => 1

theorem kcont_one : KCont one := continuous_const

theorem pcont_iker_mul (ε μ : ℝ) : PCont fun x => iker (μ + ε * x) := by
  unfold PCont iker; fun_prop

theorem abs_sub_le_one {t s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) : |t - s| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

theorem norm_kcomp_le {K L : ℝ → ℝ → ℂ} {CK CL : ℝ} {t s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hK : ∀ z ∈ Icc (0 : ℝ) 1, ‖K t z‖ ≤ CK) (hL : ∀ z ∈ Icc (0 : ℝ) 1, ‖L z s‖ ≤ CL)
    (hCK : 0 ≤ CK) (hCL : 0 ≤ CL) : ‖kcomp K L t s‖ ≤ CK * CL := by
  unfold kcomp
  have hb : ∀ z ∈ uIoc s t, ‖K t z * L z s‖ ≤ CK * CL := fun z hz => by
    have hz' := uIcc_subset_unit hs ht (uIoc_subset_uIcc hz)
    rw [norm_mul]; exact mul_le_mul (hK z hz') (hL z hz') (norm_nonneg _) hCK
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
  calc CK * CL * |t - s| ≤ CK * CL * 1 :=
        mul_le_mul_of_nonneg_left (abs_sub_le_one hs ht) (mul_nonneg hCK hCL)
    _ = CK * CL := mul_one _

/-! ### The cumulative kernel `GI θ u = ∫_0^u gk θ` -/

/-- `GI θ u = ∫_0^u gk θ`. -/
@[expose] noncomputable def GI (θ u : ℝ) : ℝ := ∫ v in (0 : ℝ)..u, gk θ v

theorem continuous_GI (θ : ℝ) : Continuous (GI θ) :=
  intervalIntegral.continuous_primitive (fun a b => (continuous_gk θ).intervalIntegrable a b) 0

theorem GI_nonneg {θ u : ℝ} (hθ : 0 < θ) (hu : 0 ≤ u) : 0 ≤ GI θ u :=
  intervalIntegral.integral_nonneg hu fun v _ => gk_nonneg hθ v

theorem GI_le_one {θ u : ℝ} (hθ : 0 < θ) (hu : 0 ≤ u) : GI θ u ≤ 1 := integral_gk_le_one hθ hu

theorem tendsto_GI {u : ℝ} (hu : 0 < u) : Tendsto (fun θ => GI θ u) (𝓝[>] 0) (𝓝 1) :=
  tendsto_integral_gk hu

/-! ### Adjacent pairs: `I_{εx} I_{μ-εx}` and Lemma 5.8's `𝒥 + ℛ` -/

/-- The kernel of `I_{εx} I_{μ-εx}`. -/
@[expose] noncomputable def pairK (ε : ℤ) (μ x t s : ℝ) : ℂ :=
  kcomp (iker (ε * x)) (iker (μ - ε * x)) t s

theorem pairK_eq (ε : ℤ) (μ x t s : ℝ) :
    pairK ε μ x t s = ∫ z in s..t, iker μ t s * cexp (π * I * (ε * x * ((z - s : ℝ) : ℂ))) := by
  unfold pairK kcomp
  refine intervalIntegral.integral_congr fun z _ => ?_
  simp only [iker, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem pcont_pairK (ε : ℤ) (μ : ℝ) : PCont (pairK ε μ) := by
  have h1 : PCont fun x => iker (ε * x) := by
    have := pcont_iker_mul ε 0; simpa using this
  have h2 : PCont fun x => iker (μ - ε * x) := by
    have := pcont_iker_mul (-ε) μ
    refine (funext fun x => ?_ : (fun x => iker (μ + -(ε : ℝ) * x)) = fun x => iker (μ - ε * x)) ▸ this
    congr 1; ring
  exact continuous_kcomp_param h1 h2

theorem norm_pairK_le (ε : ℤ) (μ x : ℝ) {t s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖pairK ε μ x t s‖ ≤ 1 := by
  have := norm_kcomp_le (K := iker (ε * x)) (L := iker (μ - ε * x)) hs ht
    (fun z _ => (norm_iker _ _ _).le) (fun z _ => (norm_iker _ _ _).le) zero_le_one zero_le_one
  simpa [pairK] using this

/-- **The regularized pair kernel**: `greg θ (x ↦ I_{εx}I_{μ-εx}(t,s)) = e^{πiμs} GI θ (t-s)`. -/
theorem greg_pairK {θ : ℝ} (hθ : 0 < θ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (μ t s : ℝ) :
    greg θ (fun x => pairK ε μ x t s) = iker μ t s * GI θ (t - s) := by
  simp_rw [pairK_eq]
  rw [greg_intervalIntegral hθ (C := 1)]
  · have e : ∀ z : ℝ, greg θ (fun x => iker μ t s * cexp (π * I * (ε * x * ((z - s : ℝ) : ℂ)))) =
        iker μ t s * gk θ (z - s) := fun z => by
      rw [greg_const_mul, greg_phase hθ hε]
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, GI,
      intervalIntegral.integral_comp_sub_right (fun v => gk θ v) s, sub_self]
  · fun_prop
  · intro x z _
    rw [norm_mul, norm_iker, one_mul]
    exact_mod_cast (norm_cexp_piI _).le

/-- `Φ` is odd. -/
theorem phiR_neg (y : ℝ) : phiR (-y) = -phiR y := by
  unfold phiR chiInvR chiInfinity
  rw [chi0_even]
  push_cast
  ring

theorem norm_phiR_le (y : ℝ) : ‖phiR y‖ ≤ CPhi := by
  unfold phiR
  have hπ : ‖(π : ℂ)‖ = π := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, hπ]
  calc ‖(chiInvR y : ℂ)‖ / π ≤ ‖(chiInvR y : ℂ)‖ / 1 :=
        div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one (by linarith [Real.two_le_pi])
    _ ≤ CPhi := by rw [div_one]; exact norm_chiInvR_le y

/-- **Lemma 5.8's `𝒥_{α,μ} + ℛ_{α,μ} = I_{εα}I_{μ-εα} + Φ(εα) I_μ`** at `α = x` (`ClassJR.TR58`). -/
@[expose] noncomputable def tr58K (ε : ℤ) (μ x t s : ℝ) : ℂ :=
  pairK ε μ x t s + phiR (ε * x) * iker μ t s

theorem TR58_eq {P : Type*} {V : Type} (σ : ℕ → V) (ε : ℕ → ℤ) (μf : ℕ → P → ℝ) (q : ℕ) (p : P)
    (α : V → ℝ) (t s : ℝ) : TR58 σ ε μf q p α t s = tr58K (ε q) (μf q p) (α (σ q)) t s := by
  simp only [TR58, sw0, phiQ, T0, tr58K, pairK]
  ring

theorem pcont_tr58K (ε : ℤ) (μ : ℝ) : PCont (tr58K ε μ) := by
  unfold tr58K
  have h := pcont_pairK ε μ
  unfold PCont at h ⊢
  have hφ : Continuous phiR := contDiff_phiR.continuous
  exact h.add ((hφ.comp (continuous_const.mul continuous_fst)).mul (by unfold iker; fun_prop))

theorem norm_tr58K_le (ε : ℤ) (μ x : ℝ) {t s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖tr58K ε μ x t s‖ ≤ 1 + CPhi := by
  unfold tr58K
  refine (norm_add_le _ _).trans (add_le_add (norm_pairK_le ε μ x hs ht) ?_)
  rw [norm_mul, norm_iker, mul_one]
  exact norm_phiR_le _

/-- **The regularized `𝒥 + ℛ` of an adjacent pair** (DH21 Lemma 7.3):
`greg θ (x ↦ tr58K ε μ x t s) = e^{πiμs} GI θ (t-s)`; the `Φ` part is odd and drops out. -/
theorem greg_tr58K {θ : ℝ} (hθ : 0 < θ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (μ : ℝ) {t s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    greg θ (fun x => tr58K ε μ x t s) = iker μ t s * GI θ (t - s) := by
  have hφ : Continuous phiR := contDiff_phiR.continuous
  have i1 : Integrable fun x => (gw θ x : ℂ) * pairK ε μ x t s :=
    integrable_gw_mul hθ ((pcont_pairK ε μ).at t s) (fun x => norm_pairK_le ε μ x hs ht)
  have i2 : Integrable fun x => (gw θ x : ℂ) * (phiR (ε * x) * iker μ t s) :=
    integrable_gw_mul hθ ((hφ.comp (continuous_const.mul continuous_id)).mul continuous_const)
      (C := CPhi) (fun x => by rw [norm_mul, norm_iker, mul_one]; exact norm_phiR_le _)
  have e : (fun x => tr58K ε μ x t s) =
      (fun x => pairK ε μ x t s) + fun x => phiR (ε * x) * iker μ t s := by
    funext x; rfl
  rw [e, greg_add i1 i2, greg_pairK hθ hε, greg_odd (F := fun x => phiR (ε * x) * iker μ t s), add_zero]
  intro x
  simp only [mul_neg, phiR_neg, neg_mul]

theorem triBdd_pairK (ε : ℤ) (μ : ℝ) : TriBdd (pairK ε μ) 1 := fun x t s hs0 hst ht1 =>
  norm_pairK_le ε μ x ⟨hs0, hst.trans ht1⟩ ⟨hs0.trans hst, ht1⟩

theorem triBdd_tr58K (ε : ℤ) (μ : ℝ) : TriBdd (tr58K ε μ) (1 + CPhi) := fun x t s hs0 hst ht1 =>
  norm_tr58K_le ε μ x ⟨hs0, hst.trans ht1⟩ ⟨hs0.trans hst, ht1⟩

/-- `gregK θ (tr58K ε μ) = e^{πiμs} GI θ (t-s)` on the triangle. -/
theorem gregK_tr58K {θ : ℝ} (hθ : 0 < θ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (μ : ℝ) {t s : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    gregK θ (tr58K ε μ) t s = iker μ t s * GI θ (t - s) :=
  greg_tr58K hθ hε μ ⟨hs0, hst.trans ht1⟩ ⟨hs0.trans hst, ht1⟩

/-! ### Non-adjacent pairs: the sandwich `I_{εx} T I_{μ-εx}` -/

/-- The kernel of the sandwich `I_{εx} T I_{μ-εx}`, right-associated: `I_{εx} (T I_{μ-εx})`. -/
@[expose] noncomputable def sandK (ε : ℤ) (μ : ℝ) (T : ℝ → ℝ → ℂ) (x t s : ℝ) : ℂ :=
  kcomp (iker (ε * x)) (kcomp T (iker (μ - ε * x))) t s

/-- `ClassJR.sandw` is the sandwich kernel `sandK` (associativity). -/
theorem sandw_eq_sandK {P : Type*} {V : Type} (ε : ℤ) (v : V) (μf : P → ℝ)
    (T : P → (V → ℝ) → ℝ → ℝ → ℂ) (p : P) (α : V → ℝ) (hT : KCont (T p α)) {t s : ℝ} (hst : s ≤ t) :
    sandw ε v μf T p α t s = sandK ε (μf p) (T p α) (α v) t s :=
  kcomp_assoc (kcont_iker _) hT (kcont_iker _) hst

theorem kcomp_iker_right (T : ℝ → ℝ → ℂ) (β y s : ℝ) :
    kcomp T (iker β) y s = kcomp T one y s * iker β y s := by
  unfold kcomp one iker
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun z _ => ?_
  ring

theorem sandK_eq (ε : ℤ) (μ : ℝ) (T : ℝ → ℝ → ℂ) (x t s : ℝ) :
    sandK ε μ T x t s = ∫ y in s..t,
      iker μ t s * cexp (π * I * (ε * x * ((y - s : ℝ) : ℂ))) * kcomp T one y s := by
  unfold sandK
  show (∫ y in s..t, iker (ε * x) t y * kcomp T (iker (μ - ε * x)) y s) = _
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [kcomp_iker_right]
  simp only [iker, ← Complex.exp_add]
  have : cexp (π * I * (ε * x * y)) * (kcomp T one y s * cexp (π * I * ((μ - ε * x) * s))) =
      kcomp T one y s * cexp (π * I * (ε * x * y) + π * I * ((μ - ε * x) * s)) := by
    rw [Complex.exp_add]; ring
  push_cast at this ⊢
  rw [this, mul_comm]
  congr 1
  congr 1
  ring

theorem pcont_sandK (ε : ℤ) (μ : ℝ) {T : ℝ → ℝ → ℂ} (hT : KCont T) : PCont (sandK ε μ T) := by
  have h1 : PCont fun x => iker (ε * x) := by
    have := pcont_iker_mul ε 0; simpa using this
  have h2 : PCont fun x => iker (μ - ε * x) := by
    have := pcont_iker_mul (-ε) μ
    refine (funext fun x => ?_ : (fun x => iker (μ + -(ε : ℝ) * x)) = fun x => iker (μ - ε * x)) ▸ this
    congr 1; ring
  exact continuous_kcomp_param h1 (continuous_kcomp_param (PCont.const hT) h2)

theorem triBdd_sandK (ε : ℤ) (μ : ℝ) {T : ℝ → ℝ → ℂ} {CT : ℝ} (hCT : 0 ≤ CT) (hT : KTriBdd T CT) :
    TriBdd (sandK ε μ T) CT := by
  intro x t s hs0 hst ht1
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hst.trans ht1⟩
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hst, ht1⟩
  unfold sandK kcomp
  have hb : ∀ y ∈ uIoc s t, ‖iker (ε * x) t y * kcomp T (iker (μ - ε * x)) y s‖ ≤ CT := by
    intro y hy
    rw [uIoc_of_le hst] at hy
    rw [norm_mul, norm_iker, one_mul]
    unfold kcomp
    have hb' : ∀ z ∈ uIoc s y, ‖T y z * iker (μ - ε * x) z s‖ ≤ CT := fun z hz => by
      rw [uIoc_of_le hy.1.le] at hz
      rw [norm_mul, norm_iker, mul_one]
      exact hT y z (hs0.trans hz.1.le) hz.2 (hy.2.trans ht1)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb').trans ?_
    have : |y - s| ≤ 1 := abs_sub_le_one hs ⟨hs0.trans hy.1.le, hy.2.trans ht1⟩
    nlinarith [abs_nonneg (y - s)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
  have : |t - s| ≤ 1 := abs_sub_le_one hs ht
  nlinarith [abs_nonneg (t - s)]

/-- The regularized sandwich `e^{πiμs} ∫_s^t gk θ(y-s) H(y,s) dy`, `H(y,s) = ∫_s^y T(y,z) dz`. -/
@[expose] noncomputable def rsandK (θ μ : ℝ) (T : ℝ → ℝ → ℂ) (t s : ℝ) : ℂ :=
  iker μ t s * ∫ y in s..t, (gk θ (y - s) : ℂ) * kcomp T one y s

/-- **The regularized sandwich.** -/
theorem gregK_sandK {θ : ℝ} (hθ : 0 < θ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (μ : ℝ) {T : ℝ → ℝ → ℂ}
    (hT : KCont T) {t s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    gregK θ (sandK ε μ T) t s = rsandK θ μ T t s := by
  obtain ⟨CT, hCT0, hCT⟩ := hT.exists_bound
  have hH : KCont (kcomp T one) := continuous_kcomp hT kcont_one
  obtain ⟨CH, -, hCH⟩ := hH.exists_bound
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨hs0, hst.trans ht1⟩
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hst, ht1⟩
  unfold gregK rsandK
  simp_rw [sandK_eq]
  rw [greg_intervalIntegral hθ (C := CH)]
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [greg_mul_const, greg_const_mul, greg_phase hθ hε]
    ring
  · exact ((continuous_const.mul (by fun_prop)).mul (hH.comp (continuous_snd.prodMk continuous_const)))
  · intro x y hy
    rw [uIcc_of_le hst] at hy
    have hy' : y ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hy.1, hy.2.trans ht1⟩
    rw [norm_mul, norm_mul, norm_iker, one_mul]
    rw [show cexp (π * I * (ε * x * ((y - s : ℝ) : ℂ))) = cexp (π * I * ((ε * x * (y - s) : ℝ) : ℂ))
      by push_cast; ring_nf, norm_cexp_piI, one_mul]
    exact hCH y s hy' hs

theorem kcont_rsandK (θ μ : ℝ) {T : ℝ → ℝ → ℂ} (hT : KCont T) : KCont (rsandK θ μ T) := by
  have hH : KCont (kcomp T one) := continuous_kcomp hT kcont_one
  have hG : KCont fun y s => (gk θ (y - s) : ℂ) * kcomp T one y s :=
    (continuous_ofReal.comp ((continuous_gk θ).comp (continuous_fst.sub continuous_snd))).mul hH
  have e : rsandK θ μ T = fun t s => iker μ t s * kcomp one (fun y s => (gk θ (y - s) : ℂ) *
      kcomp T one y s) t s := by
    funext t s; unfold rsandK kcomp one; simp only [one_mul]
  rw [e]
  exact (kcont_iker μ).mul (continuous_kcomp kcont_one hG)

/-- **The regularized sandwich tends to `0`** (DH21 Lemma 7.1: `H(s, s) = 0`). -/
theorem tendsto_rsandK (μ : ℝ) {T : ℝ → ℝ → ℂ} (hT : KCont T) {t s : ℝ} (hst : s ≤ t) :
    Tendsto (fun θ => rsandK θ μ T t s) (𝓝[>] 0) (𝓝 0) := by
  have hH : KCont (kcomp T one) := continuous_kcomp hT kcont_one
  unfold rsandK
  rcases eq_or_lt_of_le hst with rfl | hlt
  · simp
  have e : ∀ θ, (∫ y in s..t, (gk θ (y - s) : ℂ) * kcomp T one y s) =
      ∫ u in (0 : ℝ)..(t - s), (gk θ u : ℂ) * kcomp T one (u + s) s := by
    intro θ
    have h := intervalIntegral.integral_comp_sub_right
      (fun u => (gk θ u : ℂ) * kcomp T one (u + s) s) (a := s) (b := t) s
    rw [sub_self] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp
  simp_rw [e]
  have hf : ContinuousOn (fun u => kcomp T one (u + s) s) (Icc 0 (t - s)) :=
    (hH.comp ((continuous_id.add continuous_const).prodMk continuous_const)).continuousOn
  have h := tendsto_integral_gk_mul (sub_pos.2 hlt) hf
  have h0 : kcomp T one (0 + s) s = 0 := by simp [kcomp]
  rw [h0] at h
  have := h.const_mul (iker μ t s)
  rwa [mul_zero] at this

theorem kTriBdd_rsandK {θ : ℝ} (hθ : 0 < θ) (μ : ℝ) {T : ℝ → ℝ → ℂ} {CT : ℝ} (hCT : 0 ≤ CT)
    (hT : KTriBdd T CT) : KTriBdd (rsandK θ μ T) CT := by
  intro t s hs0 hst ht1
  unfold rsandK
  rw [norm_mul, norm_iker, one_mul]
  have hb : ∀ y ∈ Icc s t, ‖(gk θ (y - s) : ℂ) * kcomp T one y s‖ ≤ CT * gk θ (y - s) := by
    intro y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gk_nonneg hθ _), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (gk_nonneg hθ _)
    unfold kcomp one
    have hb' : ∀ z ∈ uIoc s y, ‖T y z * 1‖ ≤ CT := fun z hz => by
      rw [uIoc_of_le hy.1] at hz
      rw [mul_one]; exact hT y z (hs0.trans hz.1.le) hz.2 (hy.2.trans ht1)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hb').trans ?_
    have : |y - s| ≤ 1 := abs_sub_le_one ⟨hs0, hst.trans ht1⟩ ⟨hs0.trans hy.1, hy.2.trans ht1⟩
    nlinarith [abs_nonneg (y - s)]
  refine (intervalIntegral.norm_integral_le_of_norm_le hst
    (Eventually.of_forall fun y hy => hb y ⟨hy.1.le, hy.2⟩) ?_).trans ?_
  · exact ((continuous_gk θ).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
      |>.const_mul CT
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
      (fun v => gk θ v) s, sub_self]
    calc CT * ∫ v in (0 : ℝ)..(t - s), gk θ v ≤ CT * 1 :=
          mul_le_mul_of_nonneg_left (integral_gk_le_one hθ (sub_nonneg.2 hst)) hCT
      _ = CT := mul_one _

end WaveTurbulence.Cancel
