/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.RegLim

/-!
# The regularized regular chain and its limit (DH21 Lemmas 7.1–7.3, (recurtype2))

After the variables of a regular chain are integrated against their Gaussian weights, the chain
integral of DH21 (newexp2) (`ClassJR.chainT`) becomes `chainK`. Each pair `q` of the Catalan code now
carries a kernel `P q t_a t_b`; for the regularized chain this is `kk b_q θ (t_a - t_b) · R_q(t_a, t_b)`.
* `chainK P nil q t g = g t`;
* `chainK P (node i r) q t g = ∫_0^t chainK P i (q+1) t_a (t' ↦ ∫_0^{t'} P q t_a t_b ·
    chainK P r (q+|i|+1) t_b g dt_b) dt_a`.

**The limit** (`tendsto_chainK`). An adjacent pair (`inner = nil`) tends to
`∫_0^t sg(b_q) R_q(τ, τ) (⋯)(τ) dτ`. The sign `sg true = -1` for `q ∈ Z` is the F61 sign of DH21
Lemma 7.3. A non-adjacent pair tends to `0` (DH21 Lemma 7.1). The limit is `chainL`. On a dominant code
it is the iterated integral of DH21 (regchaincalref) and (recurtype2) with the factors `sg(b_q) R_q`;
otherwise it is `0`.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-- **The regularized chain** with pair kernels `P q t_a t_b`. -/
@[expose] noncomputable def chainK (P : ℕ → ℝ → ℝ → ℂ) : LegalCode → ℕ → ℝ → (ℝ → ℂ) → ℂ
  | .nil, _, t, g => g t
  | .node i r, q, t, g => ∫ ta in (0 : ℝ)..t, chainK P i (q + 1) ta
      (fun t' => ∫ tb in (0 : ℝ)..t', P q ta tb * chainK P r (q + i.size + 1) tb g)

/-- **The limit of the regularized chain**: adjacent pairs contribute `∫ D_q(τ) ⋯ dτ`, a non-adjacent
pair gives `0`. -/
@[expose] noncomputable def chainL (D : ℕ → ℝ → ℂ) : LegalCode → ℕ → ℝ → (ℝ → ℂ) → ℂ
  | .nil, _, t, g => g t
  | .node .nil r, q, t, g => ∫ τ in (0 : ℝ)..t, D q τ * chainL D r (q + 1) τ g
  | .node (.node _ _) _, _, _, _ => 0

theorem chainK_nil (P : ℕ → ℝ → ℝ → ℂ) (q : ℕ) (t : ℝ) (g : ℝ → ℂ) : chainK P .nil q t g = g t := rfl

theorem chainK_node (P : ℕ → ℝ → ℝ → ℂ) (i r : LegalCode) (q : ℕ) (t : ℝ) (g : ℝ → ℂ) :
    chainK P (.node i r) q t g = ∫ ta in (0 : ℝ)..t, chainK P i (q + 1) ta
      (fun t' => ∫ tb in (0 : ℝ)..t', P q ta tb * chainK P r (q + i.size + 1) tb g) := rfl

theorem chainL_zero (D : ℕ → ℝ → ℂ) : ∀ (c : LegalCode) (q : ℕ) (t : ℝ),
    chainL D c q t (fun _ => 0) = 0
  | .nil, _, _ => rfl
  | .node .nil r, q, t => by
    simp only [chainL]
    simp [chainL_zero D r (q + 1)]
  | .node (.node _ _) _, _, _ => rfl

/-! ### Continuity and bounds -/

/-- **Continuity of the regularized chain** in the time and in parameters. -/
theorem continuous_chainK {P : ℕ → ℝ → ℝ → ℂ} (hP : ∀ j, Continuous (Function.uncurry (P j))) :
    ∀ (c : LegalCode) (q : ℕ) {X : Type} [TopologicalSpace X] {g : X → ℝ → ℂ}
      (_ : Continuous (Function.uncurry g)),
      Continuous fun p : X × ℝ => chainK P c q p.2 (g p.1)
  | .nil, _, _, _, _, hg => hg
  | .node i r, q, X, _, g, hg => by
    simp_rw [chainK_node]
    have hR := continuous_chainK hP r (q + i.size + 1) hg
    have hE : Continuous fun p : (X × ℝ) × ℝ => ∫ tb in (0 : ℝ)..p.2,
        P q p.1.2 tb * chainK P r (q + i.size + 1) tb (g p.1.1) := by
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : (X × ℝ) × ℝ) (tb : ℝ) => P q p.1.2 tb * chainK P r (q + i.size + 1) tb (g p.1.1))
        ?_ continuous_snd
      exact ((hP q).comp (f := fun p : ((X × ℝ) × ℝ) × ℝ => (p.1.1.2, p.2)) (by fun_prop)).mul
        (hR.comp (f := fun p : ((X × ℝ) × ℝ) × ℝ => (p.1.1.1, p.2)) (by fun_prop))
    have hI := continuous_chainK hP i (q + 1) (X := X × ℝ)
      (g := fun (x : X × ℝ) (t' : ℝ) => ∫ tb in (0 : ℝ)..t',
        P q x.2 tb * chainK P r (q + i.size + 1) tb (g x.1)) hE
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : X × ℝ) (ta : ℝ) => chainK P i (q + 1) ta (fun t' => ∫ tb in (0 : ℝ)..t',
        P q ta tb * chainK P r (q + i.size + 1) tb (g p.1))) ?_ continuous_snd
    exact hI.comp (f := fun p : (X × ℝ) × ℝ => ((p.1.1, p.2), p.2)) (by fun_prop)

theorem continuous_chainK' {P : ℕ → ℝ → ℝ → ℂ} (hP : ∀ j, Continuous (Function.uncurry (P j)))
    (c : LegalCode) (q : ℕ) {g : ℝ → ℂ} (hg : Continuous g) : Continuous fun t => chainK P c q t g := by
  have h := continuous_chainK hP c q (X := Unit) (g := fun _ => g) (hg.comp continuous_snd)
  exact h.comp (f := fun t : ℝ => ((), t)) (continuous_const.prodMk continuous_id)

/-- **The bound** `‖chainK‖ ≤ m^{|c|} sup|g|` when every pair kernel has mass at most `m`. -/
theorem norm_chainK_le {P : ℕ → ℝ → ℝ → ℂ} {m : ℝ} (hm : 0 ≤ m)
    (hP : ∀ j, ∀ ta ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1, ∀ (f : ℝ → ℂ) (G : ℝ),
      (∀ y ∈ Icc (0 : ℝ) x, ‖f y‖ ≤ G) → ‖∫ tb in (0 : ℝ)..x, P j ta tb * f tb‖ ≤ m * max G 0) :
    ∀ (c : LegalCode) (q : ℕ) {g : ℝ → ℂ} {G : ℝ} (_ : 0 ≤ G),
      (∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ G) → ∀ t ∈ Icc (0 : ℝ) 1, ‖chainK P c q t g‖ ≤ m ^ c.size * G
  | .nil, _, _, _, _, hg, t, ht => by
    rw [chainK_nil, show LegalCode.nil.size = 0 from rfl, pow_zero, one_mul]; exact hg t ht
  | .node i r, q, g, G, hG, hg, t, ht => by
    rw [chainK_node]
    have hr := norm_chainK_le hm hP r (q + i.size + 1) hG hg
    have hrG : 0 ≤ m ^ r.size * G := by positivity
    have hcont : ∀ ta ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1,
        ‖∫ tb in (0 : ℝ)..x, P q ta tb * chainK P r (q + i.size + 1) tb g‖ ≤ m * (m ^ r.size * G) := by
      intro ta hta x hx
      have := hP q ta hta x hx (fun tb => chainK P r (q + i.size + 1) tb g) (m ^ r.size * G)
        fun y hy => hr y ⟨hy.1, hy.2.trans hx.2⟩
      rwa [max_eq_left hrG] at this
    have hF : ∀ ta ∈ uIoc (0 : ℝ) t, ‖chainK P i (q + 1) ta (fun t' => ∫ tb in (0 : ℝ)..t',
        P q ta tb * chainK P r (q + i.size + 1) tb g)‖ ≤ m ^ i.size * (m * (m ^ r.size * G)) := by
      intro ta hta
      rw [uIoc_of_le ht.1] at hta
      have hta' : ta ∈ Icc (0 : ℝ) 1 := ⟨hta.1.le, hta.2.trans ht.2⟩
      exact norm_chainK_le hm hP i (q + 1) (by positivity) (hcont ta hta') ta hta'
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hF).trans ?_
    rw [sub_zero, abs_of_nonneg ht.1]
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    rw [hsz, pow_add, pow_add, pow_one]
    have h0 : 0 ≤ m ^ i.size * (m * (m ^ r.size * G)) := by positivity
    nlinarith [ht.2]

/-! ### Fubini on the triangle -/

theorem integral_lower_eq_ite {f : ℝ → ℂ} (hf : Continuous f) {ta t : ℝ} (h0 : 0 ≤ ta)
    (hta : ta ≤ t) : ∫ tb in (0 : ℝ)..ta, f tb = ∫ tb in (0 : ℝ)..t, if tb ≤ ta then f tb else 0 := by
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun tb => if tb ≤ ta then f tb else 0) volume x y := by
    intro x y
    have : (fun tb => if tb ≤ ta then f tb else 0) = (Iic ta).indicator f := by
      funext tb; simp [Set.indicator, Set.mem_Iic]
    rw [this]
    exact ⟨(hf.intervalIntegrable x y).1.indicator measurableSet_Iic,
      (hf.intervalIntegrable x y).2.indicator measurableSet_Iic⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := ta) (hi 0 ta) (hi ta t)]
  have h1 : ∫ tb in (0 : ℝ)..ta, (if tb ≤ ta then f tb else 0) = ∫ tb in (0 : ℝ)..ta, f tb := by
    refine intervalIntegral.integral_congr fun tb htb => ?_
    rw [uIcc_of_le h0] at htb
    simp [htb.2]
  have h2 : ∫ tb in ta..t, (if tb ≤ ta then f tb else 0) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℂ)) ?_]
    · simp
    · refine Eventually.of_forall fun tb htb => ?_
      rw [uIoc_of_le hta] at htb
      simp [not_le.2 htb.1]
  rw [h1, h2, add_zero]

theorem integral_upper_eq_ite {f : ℝ → ℂ} (hf : Continuous f) {tb t : ℝ} (h0 : 0 ≤ tb)
    (htb : tb ≤ t) : ∫ ta in tb..t, f ta = ∫ ta in (0 : ℝ)..t, if tb ≤ ta then f ta else 0 := by
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun ta => if tb ≤ ta then f ta else 0) volume x y := by
    intro x y
    have : (fun ta => if tb ≤ ta then f ta else 0) = (Ici tb).indicator f := by
      funext ta; simp [Set.indicator, Set.mem_Ici]
    rw [this]
    exact ⟨(hf.intervalIntegrable x y).1.indicator measurableSet_Ici,
      (hf.intervalIntegrable x y).2.indicator measurableSet_Ici⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := tb) (hi 0 tb) (hi tb t)]
  have h1 : ∫ ta in (0 : ℝ)..tb, (if tb ≤ ta then f ta else 0) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℂ)) ?_]
    · simp
    · filter_upwards [Measure.ae_ne volume tb] with ta hne hta
      rw [uIoc_of_le h0] at hta
      simp [not_le.2 (lt_of_le_of_ne hta.2 hne)]
  have h2 : ∫ ta in tb..t, (if tb ≤ ta then f ta else 0) = ∫ ta in tb..t, f ta := by
    refine intervalIntegral.integral_congr fun ta hta => ?_
    rw [uIcc_of_le htb] at hta
    simp [hta.1]
  rw [h1, h2, zero_add]

/-- **Fubini on the triangle** `0 ≤ t_b ≤ t_a ≤ t`. -/
theorem integral_triangle_swap {f : ℝ → ℝ → ℂ} (hf : Continuous (Function.uncurry f)) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫ ta in (0 : ℝ)..t, ∫ tb in (0 : ℝ)..ta, f ta tb = ∫ tb in (0 : ℝ)..t, ∫ ta in tb..t, f ta tb := by
  set F : ℝ → ℝ → ℂ := fun ta tb => if tb ≤ ta then f ta tb else 0 with hF
  have hL : ∫ ta in (0 : ℝ)..t, ∫ tb in (0 : ℝ)..ta, f ta tb =
      ∫ ta in (0 : ℝ)..t, ∫ tb in (0 : ℝ)..t, F ta tb := by
    refine intervalIntegral.integral_congr fun ta hta => ?_
    rw [uIcc_of_le ht] at hta
    exact integral_lower_eq_ite (hf.comp (continuous_const.prodMk continuous_id)) hta.1 hta.2
  have hR : ∫ tb in (0 : ℝ)..t, ∫ ta in tb..t, f ta tb =
      ∫ tb in (0 : ℝ)..t, ∫ ta in (0 : ℝ)..t, F ta tb := by
    refine intervalIntegral.integral_congr fun tb htb => ?_
    rw [uIcc_of_le ht] at htb
    exact integral_upper_eq_ite (hf.comp (continuous_id.prodMk continuous_const)) htb.1 htb.2
  rw [hL, hR]
  refine intervalIntegral_intervalIntegral_swap ?_
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := t))).exists_bound_of_continuousOn
    (hf.continuousOn (s := Icc (0 : ℝ) t ×ˢ Icc 0 t))
  have hmeas : Measurable (Function.uncurry F) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst) hf.measurable measurable_const
  refine Measure.integrableOn_of_bounded (M := C) ?_ hmeas.aestronglyMeasurable ?_
  · rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by simp [Set.uIoc]) (by simp [Set.uIoc])
  · refine ae_restrict_of_forall_mem (measurableSet_uIoc.prod measurableSet_uIoc) fun p hp => ?_
    rw [Set.uIoc_of_le ht] at hp
    have hp' : p ∈ Icc (0 : ℝ) t ×ˢ Icc 0 t := ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩
    simp only [Function.uncurry, hF]
    split_ifs
    · exact hC p hp'
    · simp only [norm_zero]; exact (norm_nonneg _).trans (hC p hp')

/-! ### The limit -/

/-- **A family of pair coefficients with regularized limits**: continuous, uniformly bounded and
uniformly Lipschitz (eventually in `θ`), converging on the square. -/
structure KFam (R : ℕ → ℝ → ℝ → ℝ → ℂ) (R₀ : ℕ → ℝ → ℝ → ℂ) : Prop where
  bound : ∃ M, ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ j ta tb, ‖R j θ ta tb‖ ≤ M
  lip : ∃ L, ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ j ta tb ta' tb',
    ‖R j θ ta tb - R j θ ta' tb'‖ ≤ L * (|ta - ta'| + |tb - tb'|)
  lim : ∀ j, ∀ ta ∈ Icc (0 : ℝ) 1, ∀ tb ∈ Icc (0 : ℝ) 1,
    Tendsto (fun θ => R j θ ta tb) (𝓝[>] 0) (𝓝 (R₀ j ta tb))

/-- The regularized pair kernels `kk b_j θ (t_a - t_b) R_j(t_a, t_b)`. -/
@[expose] noncomputable def kP (bb : ℕ → Bool) (R : ℕ → ℝ → ℝ → ℝ → ℂ) (θ : ℝ) (j : ℕ)
    (ta tb : ℝ) : ℂ := (kk (bb j) θ (ta - tb) : ℂ) * R j θ ta tb

/-- The limit densities `sg(b_j) R_j(τ, τ)`. -/
@[expose] noncomputable def kD (bb : ℕ → Bool) (R₀ : ℕ → ℝ → ℝ → ℂ) (j : ℕ) (τ : ℝ) : ℂ :=
  sg (bb j) * R₀ j τ τ

section Limit

variable {bb : ℕ → Bool} {R : ℕ → ℝ → ℝ → ℝ → ℂ} {R₀ : ℕ → ℝ → ℝ → ℂ}

theorem KFam.cont (hR : KFam R R₀) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ j, Continuous (Function.uncurry (R j θ)) := by
  obtain ⟨L, hL⟩ := hR.lip
  exact hL.mono fun θ hθ j => continuous_of_lip2 (hθ j)

theorem continuous_kP (hR : KFam R R₀) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ j, Continuous (Function.uncurry (kP bb R θ j)) := by
  filter_upwards [hR.cont] with θ hθ j
  exact (continuous_ofReal.comp ((continuous_kk _ θ).comp (continuous_fst.sub continuous_snd))).mul
    (hθ j)

theorem mass_kP (hR : KFam R R₀) : ∃ m, 0 ≤ m ∧ ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ j, ∀ ta ∈ Icc (0 : ℝ) 1,
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ (f : ℝ → ℂ) (G : ℝ), (∀ y ∈ Icc (0 : ℝ) x, ‖f y‖ ≤ G) →
      ‖∫ tb in (0 : ℝ)..x, kP bb R θ j ta tb * f tb‖ ≤ m * max G 0 := by
  obtain ⟨M, hM⟩ := hR.bound
  refine ⟨2 * max M 0, by positivity, ?_⟩
  filter_upwards [hM, eventually_pos_nhdsGT] with θ hθM hθ j ta _ x hx f G hG
  have := norm_integral_kk_shift_le (b := bb j) hθ ta hx.1 (f := fun tb => R j θ ta tb * f tb)
    (B := max M 0 * max G 0) fun y hy => by
      rw [norm_mul]
      exact mul_le_mul ((hθM j ta y).trans (le_max_left _ _)) ((hG y hy).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)
  simp only [kP]
  refine (le_of_eq_of_le (congrArg norm (intervalIntegral.integral_congr fun tb _ => by ring)) this).trans ?_
  rw [max_eq_left (by positivity)]
  ring_nf; rfl

theorem continuous_integral_from {f : ℝ → ℝ → ℂ} (hf : Continuous (Function.uncurry f)) (t : ℝ) :
    Continuous fun x => ∫ y in x..t, f x y := by
  have e : (fun x => ∫ y in x..t, f x y) =
      fun x => (∫ y in (0 : ℝ)..t, f x y) - ∫ y in (0 : ℝ)..x, f x y := by
    funext x
    have hc : Continuous fun y => f x y := hf.comp (continuous_const.prodMk continuous_id)
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 t)
      (hc.intervalIntegrable 0 x)]
  rw [e]
  exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 t).sub
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_id)

/-- **The limit of the regularized chain** (DH21 Lemmas 7.1, 7.3; (recurtype2)). The continuation
`g_θ` must be continuous, uniformly bounded, and convergent on `[0, t)` (and at `t` for the empty
chain). -/
theorem tendsto_chainK (hR : KFam R R₀) :
    ∀ (c : LegalCode) (q : ℕ) {g : ℝ → ℝ → ℂ} {g₀ : ℝ → ℂ} {G : ℝ},
      (∀ᶠ θ in 𝓝[>] (0 : ℝ), Continuous (g θ)) →
      (∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ x ∈ Icc (0 : ℝ) 1, ‖g θ x‖ ≤ G) →
      ∀ t ∈ Icc (0 : ℝ) 1, (∀ x ∈ Ico (0 : ℝ) t, Tendsto (fun θ => g θ x) (𝓝[>] 0) (𝓝 (g₀ x))) →
      (c = .nil → Tendsto (fun θ => g θ t) (𝓝[>] 0) (𝓝 (g₀ t))) →
      Tendsto (fun θ => chainK (kP bb R θ) c q t (g θ)) (𝓝[>] 0) (𝓝 (chainL (kD bb R₀) c q t g₀))
  | .nil, _, _, _, _, _, _, t, _, _, hnil => hnil rfl
  | .node .nil r, q, g, g₀, G, hgc, hgG, t, ht, hlim, _ => by
    obtain ⟨m, hm0, hm⟩ := mass_kP (bb := bb) hR
    obtain ⟨M, hM⟩ := hR.bound
    obtain ⟨L, hL⟩ := hR.lip
    -- the rest of the chain
    set C : ℝ → ℝ → ℂ := fun θ tb => chainK (kP bb R θ) r (q + 1) tb (g θ) with hC
    have hCc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Continuous (C θ) := by
      filter_upwards [continuous_kP (bb := bb) hR, hgc] with θ hP hg
      exact continuous_chainK' hP r (q + 1) hg
    have hCb : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ tb ∈ Icc (0 : ℝ) 1, ‖C θ tb‖ ≤ m ^ r.size * max G 0 := by
      filter_upwards [hm, hgG] with θ hθm hθG tb htb
      exact norm_chainK_le hm0 hθm r (q + 1) (le_max_right _ _)
        (fun x hx => (hθG x hx).trans (le_max_left _ _)) tb htb
    -- the swapped form `∫_0^t W(t, t_b) C(t_b) dt_b`
    set W : ℝ → ℝ → ℂ := fun θ tb => ∫ ta in tb..t, kP bb R θ q ta tb with hW
    have hswap : ∀ᶠ θ in 𝓝[>] (0 : ℝ), chainK (kP bb R θ) (.node .nil r) q t (g θ) =
        ∫ tb in (0 : ℝ)..t, W θ tb * C θ tb := by
      filter_upwards [continuous_kP (bb := bb) hR, hCc] with θ hP hCθ
      rw [chainK_node]
      have e : (fun ta => chainK (kP bb R θ) .nil (q + 1) ta (fun t' => ∫ tb in (0 : ℝ)..t',
          kP bb R θ q ta tb * chainK (kP bb R θ) r (q + LegalCode.nil.size + 1) tb (g θ))) =
          fun ta => ∫ tb in (0 : ℝ)..ta, kP bb R θ q ta tb * C θ tb := rfl
      have hcont : Continuous (Function.uncurry fun ta tb => kP bb R θ q ta tb * C θ tb) :=
        (hP q).mul (hCθ.comp continuous_snd)
      rw [e, integral_triangle_swap hcont ht.1]
      exact intervalIntegral.integral_congr fun tb _ => intervalIntegral.integral_mul_const _ _
    have hWc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Continuous (W θ) := by
      filter_upwards [continuous_kP (bb := bb) hR] with θ hP
      exact continuous_integral_from (f := fun tb ta => kP bb R θ q ta tb)
        ((hP q).comp continuous_swap) t
    have hWb : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ tb ∈ Icc (0 : ℝ) t, ‖W θ tb‖ ≤ 2 * max M 0 := by
      filter_upwards [hM, eventually_pos_nhdsGT] with θ hθM hθ tb htb
      exact norm_integral_kk_shift_le' (b := bb q) hθ tb htb.2 (f := fun ta => R q θ ta tb)
        fun x _ => hθM q x tb
    refine Tendsto.congr' (EventuallyEq.symm hswap) ?_
    simp only [chainL, kD]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => 2 * max M 0 * (m ^ r.size * max G 0)) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hWc, hCc] with θ hWθ hCθ
      exact (hWθ.mul hCθ).aestronglyMeasurable
    · filter_upwards [hWb, hCb] with θ hWθ hCθ
      refine Eventually.of_forall fun tb htb => ?_
      rw [uIoc_of_le ht.1] at htb
      rw [norm_mul]
      exact mul_le_mul (hWθ tb ⟨htb.1.le, htb.2⟩) (hCθ tb ⟨htb.1.le, htb.2.trans ht.2⟩)
        (norm_nonneg _) (by positivity)
    · filter_upwards [Measure.ae_ne volume t] with tb hne htb
      rw [uIoc_of_le ht.1] at htb
      have htb' : tb < t := lt_of_le_of_ne htb.2 hne
      have htb1 : tb ∈ Icc (0 : ℝ) 1 := ⟨htb.1.le, htb.2.trans ht.2⟩
      -- the kernel `W`
      have hWlim : Tendsto (fun θ => W θ tb) (𝓝[>] 0) (𝓝 (sg (bb q) * R₀ q tb tb)) := by
        have e : ∀ θ, W θ tb = ∫ u in (0 : ℝ)..(t - tb), (kk (bb q) θ u : ℂ) * R q θ (u + tb) tb := by
          intro θ
          have e := intervalIntegral.integral_comp_sub_right
            (fun u => (kk (bb q) θ u : ℂ) * R q θ (u + tb) tb) (a := tb) (b := t) tb
          simp only [sub_add_cancel, sub_self] at e
          exact e
        simp_rw [e]
        refine tendsto_integral_kk_mul_of_lip (sub_pos.2 htb') ?_ (L := max L 0) ?_ ?_
        · filter_upwards [hR.cont] with θ hθ
          exact (hθ q |>.comp ((continuous_id.add continuous_const).prodMk continuous_const)).continuousOn
        · filter_upwards [hL] with θ hθ u hu
          have := hθ q (u + tb) tb (0 + tb) tb
          simp only [zero_add, add_sub_cancel_right, sub_self, abs_zero, add_zero] at this
          rw [zero_add, abs_of_nonneg hu.1] at *
          exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1)
        · simpa using hR.lim q tb htb1 tb htb1
      -- the rest of the chain
      have hClim := tendsto_chainK hR r (q + 1) hgc hgG tb htb1
        (fun x hx => hlim x ⟨hx.1, hx.2.trans htb'⟩) fun _ => hlim tb ⟨htb.1.le, htb'⟩
      exact hWlim.mul hClim
  | .node (.node a b) r, q, g, g₀, G, hgc, hgG, t, ht, hlim, _ => by
    obtain ⟨m, hm0, hm⟩ := mass_kP (bb := bb) hR
    obtain ⟨M, hM⟩ := hR.bound
    set C : ℝ → ℝ → ℂ := fun θ tb =>
      chainK (kP bb R θ) r (q + (LegalCode.node a b).size + 1) tb (g θ) with hC
    have hCc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Continuous (C θ) := by
      filter_upwards [continuous_kP (bb := bb) hR, hgc] with θ hP hg
      exact continuous_chainK' hP r _ hg
    have hCb : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ tb ∈ Icc (0 : ℝ) 1, ‖C θ tb‖ ≤ m ^ r.size * max G 0 := by
      filter_upwards [hm, hgG] with θ hθm hθG tb htb
      exact norm_chainK_le hm0 hθm r _ (le_max_right _ _)
        (fun x hx => (hθG x hx).trans (le_max_left _ _)) tb htb
    -- the continuation of the inner block
    set K : ℝ → ℝ → ℝ → ℂ := fun θ ta t' => ∫ tb in (0 : ℝ)..t', kP bb R θ q ta tb * C θ tb with hK
    have hKc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Continuous (Function.uncurry (K θ)) := by
      filter_upwards [continuous_kP (bb := bb) hR, hCc] with θ hP hCθ
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × ℝ) tb => kP bb R θ q p.1 tb * C θ tb)
        (((hP q).comp (continuous_fst.fst.prodMk continuous_snd)).mul (hCθ.comp continuous_snd))
        continuous_snd
    have hKb : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ ta ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1,
        ‖K θ ta x‖ ≤ m * (m ^ r.size * max G 0) := by
      filter_upwards [hm, hCb] with θ hθm hθC ta hta x hx
      have := hθm q ta hta x hx (C θ) (m ^ r.size * max G 0)
        fun y hy => hθC y ⟨hy.1, hy.2.trans hx.2⟩
      rwa [max_eq_left (by positivity)] at this
    have hF : ∀ᶠ θ in 𝓝[>] (0 : ℝ), chainK (kP bb R θ) (.node (.node a b) r) q t (g θ) =
        ∫ ta in (0 : ℝ)..t, chainK (kP bb R θ) (.node a b) (q + 1) ta (K θ ta) :=
      Eventually.of_forall fun θ => rfl
    refine Tendsto.congr' (EventuallyEq.symm hF) ?_
    simp only [chainL]
    rw [show (0 : ℂ) = ∫ ta in (0 : ℝ)..t, (0 : ℂ) by simp]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => m ^ (LegalCode.node a b).size * (m * (m ^ r.size * max G 0))) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [continuous_kP (bb := bb) hR, hKc] with θ hP hKθ
      have h := continuous_chainK hP (.node a b) (q + 1) (X := ℝ) (g := K θ) hKθ
      exact (h.comp (continuous_id.prodMk continuous_id)).aestronglyMeasurable
    · filter_upwards [hm, hKb] with θ hθm hθK
      refine Eventually.of_forall fun ta hta => ?_
      rw [uIoc_of_le ht.1] at hta
      have hta' : ta ∈ Icc (0 : ℝ) 1 := ⟨hta.1.le, hta.2.trans ht.2⟩
      exact norm_chainK_le hm0 hθm (.node a b) (q + 1) (by positivity) (hθK ta hta') ta hta'
    · refine Eventually.of_forall fun ta hta => ?_
      rw [uIoc_of_le ht.1] at hta
      have hta' : ta ∈ Icc (0 : ℝ) 1 := ⟨hta.1.le, hta.2.trans ht.2⟩
      -- the continuation tends to `0` below `ta` (the tail of the kernel)
      have hKlim : ∀ x ∈ Ico (0 : ℝ) ta, Tendsto (fun θ => K θ ta x) (𝓝[>] 0) (𝓝 0) := by
        intro x hx
        have e : ∀ θ, K θ ta x = ∫ u in (ta - x)..ta, (kk (bb q) θ u : ℂ) * (R q θ ta (ta - u) *
            C θ (ta - u)) := by
          intro θ
          have e := intervalIntegral.integral_comp_sub_left
            (fun u => (kk (bb q) θ u : ℂ) * (R q θ ta (ta - u) * C θ (ta - u))) (a := 0) (b := x) ta
          simp only [sub_sub_cancel, sub_zero] at e
          rw [← e]
          exact intervalIntegral.integral_congr fun tb _ => by simp only [kP]; ring
        simp_rw [e]
        exact tendsto_integral_kk_tail (sub_pos.2 hx.2) (by linarith [hx.1])
          (M := max M 0 * (m ^ r.size * max G 0)) (by
            filter_upwards [hM, hCb] with θ hθM hθC u hu
            have hu' : ta - u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1, hta'.2, hx.2]⟩
            rw [norm_mul]
            exact mul_le_mul ((hθM q ta (ta - u)).trans (le_max_left _ _)) (hθC _ hu')
              (norm_nonneg _) (le_max_right _ _))
      have := tendsto_chainK hR (.node a b) (q + 1) (g := fun θ => K θ ta) (g₀ := fun _ => 0)
        (hKc.mono fun θ hθ => hθ.comp (continuous_const.prodMk continuous_id))
        (hKb.mono fun θ hθ x hx => hθ ta hta' x hx) ta hta' hKlim (fun h => by cases h)
      rwa [chainL_zero] at this

end Limit

/-! ### Linearity and Lipschitz bounds -/

/-- `chainK` is linear in the continuation. -/
theorem chainK_sub {P : ℕ → ℝ → ℝ → ℂ} (hP : ∀ j, Continuous (Function.uncurry (P j))) :
    ∀ (c : LegalCode) (q : ℕ) {h₁ h₂ : ℝ → ℂ}, Continuous h₁ → Continuous h₂ → ∀ t : ℝ,
      chainK P c q t h₁ - chainK P c q t h₂ = chainK P c q t (fun x => h₁ x - h₂ x)
  | .nil, _, _, _, _, _, _ => rfl
  | .node i r, q, h₁, h₂, hh₁, hh₂, t => by
    simp only [chainK_node]
    have hr := chainK_sub hP r (q + i.size + 1) hh₁ hh₂
    have hc : ∀ h : ℝ → ℂ, Continuous h → Continuous (Function.uncurry fun (ta t' : ℝ) =>
        ∫ tb in (0 : ℝ)..t', P q ta tb * chainK P r (q + i.size + 1) tb h) := fun h hh =>
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × ℝ) tb => P q p.1 tb * chainK P r (q + i.size + 1) tb h)
        (((hP q).comp (continuous_fst.fst.prodMk continuous_snd)).mul
          ((continuous_chainK' hP r _ hh).comp continuous_snd)) continuous_snd
    have hF : ∀ h : ℝ → ℂ, Continuous h → Continuous fun ta => chainK P i (q + 1) ta
        (fun t' => ∫ tb in (0 : ℝ)..t', P q ta tb * chainK P r (q + i.size + 1) tb h) := fun h hh =>
      (continuous_chainK hP i (q + 1) (hc h hh)).comp (continuous_id.prodMk continuous_id)
    rw [← intervalIntegral.integral_sub ((hF h₁ hh₁).intervalIntegrable _ _)
      ((hF h₂ hh₂).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun ta _ => ?_
    have hci : ∀ h : ℝ → ℂ, Continuous h → Continuous fun t' =>
        ∫ tb in (0 : ℝ)..t', P q ta tb * chainK P r (q + i.size + 1) tb h := fun h hh =>
      (hc h hh).comp (continuous_const.prodMk continuous_id)
    rw [chainK_sub hP i (q + 1) (hci h₁ hh₁) (hci h₂ hh₂) ta]
    congr 1
    funext t'
    have hrc : ∀ h : ℝ → ℂ, Continuous h → Continuous fun tb =>
        P q ta tb * chainK P r (q + i.size + 1) tb h := fun h hh =>
      ((hP q).comp (continuous_const.prodMk continuous_id)).mul (continuous_chainK' hP r _ hh)
    rw [← intervalIntegral.integral_sub ((hrc h₁ hh₁).intervalIntegrable _ _)
      ((hrc h₂ hh₂).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun tb _ => ?_
    show P q ta tb * chainK P r (q + i.size + 1) tb h₁ - P q ta tb * chainK P r (q + i.size + 1) tb h₂ =
      P q ta tb * chainK P r (q + i.size + 1) tb (fun x => h₁ x - h₂ x)
    rw [← mul_sub, hr tb]

/-- **`chainK` is Lipschitz in the time** (a nonempty chain, with bounded kernels' masses). -/
theorem chainK_lip {P : ℕ → ℝ → ℝ → ℂ} {m : ℝ} (hm : 0 ≤ m)
    (hP : ∀ j, ∀ ta ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1, ∀ (f : ℝ → ℂ) (G : ℝ),
      (∀ y ∈ Icc (0 : ℝ) x, ‖f y‖ ≤ G) → ‖∫ tb in (0 : ℝ)..x, P j ta tb * f tb‖ ≤ m * max G 0)
    (i r : LegalCode) (q : ℕ) {g : ℝ → ℂ} {G : ℝ} (hG : 0 ≤ G) (hg : ∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ G)
    (hPc : ∀ j, Continuous (Function.uncurry (P j))) (hgc : Continuous g)
    {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1) :
    ‖chainK P (.node i r) q t g - chainK P (.node i r) q t' g‖ ≤
      m ^ i.size * (m * (m ^ r.size * G)) * |t - t'| := by
  simp only [chainK_node]
  have hr := norm_chainK_le hm hP r (q + i.size + 1) hG hg
  have hrG : 0 ≤ m ^ r.size * G := by positivity
  have hcont : ∀ ta ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖∫ tb in (0 : ℝ)..x, P q ta tb * chainK P r (q + i.size + 1) tb g‖ ≤ m * (m ^ r.size * G) := by
    intro ta hta x hx
    have := hP q ta hta x hx (fun tb => chainK P r (q + i.size + 1) tb g) (m ^ r.size * G)
      fun y hy => hr y ⟨hy.1, hy.2.trans hx.2⟩
    rwa [max_eq_left hrG] at this
  have hFc : Continuous fun ta => chainK P i (q + 1) ta
      (fun t' => ∫ tb in (0 : ℝ)..t', P q ta tb * chainK P r (q + i.size + 1) tb g) := by
    have hc : Continuous (Function.uncurry fun (ta t' : ℝ) =>
        ∫ tb in (0 : ℝ)..t', P q ta tb * chainK P r (q + i.size + 1) tb g) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × ℝ) tb => P q p.1 tb * chainK P r (q + i.size + 1) tb g)
        (((hPc q).comp (continuous_fst.fst.prodMk continuous_snd)).mul
          ((continuous_chainK' hPc r _ hgc).comp continuous_snd)) continuous_snd
    exact (continuous_chainK hPc i (q + 1) hc).comp (continuous_id.prodMk continuous_id)
  rw [intervalIntegral.integral_interval_sub_left (hFc.intervalIntegrable _ _)
    (hFc.intervalIntegrable _ _)]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun ta hta => ?_
  have hta' : ta ∈ Icc (0 : ℝ) 1 := by
    have := uIoc_subset_uIcc hta
    rw [mem_uIcc] at this
    rcases this with h | h
    · exact ⟨ht'.1.trans h.1, h.2.trans ht.2⟩
    · exact ⟨ht.1.trans h.1, h.2.trans ht'.2⟩
  exact norm_chainK_le hm hP i (q + 1) (by positivity) (hcont ta hta') ta hta'

end WaveTurbulence.Cancel
