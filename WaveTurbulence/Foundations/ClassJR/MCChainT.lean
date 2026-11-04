/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCType1

/-!
# The time integral of a regular chain (DH21 (newexp2))

DH21 (newexp2) (L928–L933) writes the coefficient of a type 2 couple as an iterated integral over
`t > t₁ > ⋯ > t_{2m} > 0` with the phases `e^{πiβ_a t_a}` and, for each pair `{a, b}` of the legal
partition, the coefficient `F_j(t_a, t_b)` of the two subcouples attached to the pair. For a legal
partition in Catalan form (`LegalCode`: the first pair `{a, b}` encloses the block `inner` and is
followed by the block `rest`), this iterated integral is the continuation-passing recursion
`chainT`:
* `chainT nil q F α t g = g t`;
* `chainT (node i r) q F α t g = ∫_0^t e^{πiε_qα_q t_a} chainT i (q+1) F α t_a
    (t' ↦ ∫_0^{t'} e^{-πiε_qα_q t_b} F_q(t_a, t_b) chainT r (q+|i|+1) F α t_b g dt_b) dt_a`,
where `g` is the integrand at the last time `t_{2m}` (the lone-pair factor). Pairs `j` have variable
`α_j = α (σ j)` and sign `ε_j` (DH21 L930: `β_a = ε_jα_j`, `β_b = -ε_jα_j`).

* `chainT_exp`: when `F_j(t_a, t_b) = e^{πi(λ_{j,1}t_a + λ_{j,2}t_b)}`, `chainT` is the Volterra
  operator of the pure chain `I_{β₁+λ₁} ⋯ I_{β_{2m}+λ_{2m}}` (`pchain`, DH21 (regchaink),
  (kusingI)) in the translated variables `α̃_j = α_j + ε_jλ_{j,1}` with `μ_j = λ_{j,1} + λ_{j,2}`
  (DH21 (translationk)).
* `volterra_kcomp`: the Volterra operator of a kernel composition is the composition.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Volterra

/-- **The Volterra operator of a composition** is the composition of the Volterra operators. -/
theorem volterra_kcomp {K L : ℝ → ℝ → ℂ} (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hL : Continuous fun p : ℝ × ℝ => L p.1 p.2) {g : ℝ → ℂ} (hg : Continuous g) {t : ℝ}
    (ht : 0 ≤ t) : volterra (kcomp K L) g t = volterra K (volterra L g) t := by
  -- the integrand on the square, `f z s = K t z L z s g s`
  set f : ℝ → ℝ → ℂ := fun z s => K t z * L z s * g s with hf
  have hfc : Continuous fun p : ℝ × ℝ => f p.2 p.1 := by
    simp only [hf]
    exact ((hK.comp (continuous_const.prodMk continuous_snd)).mul
      (hL.comp (continuous_snd.prodMk continuous_fst))).mul (hg.comp continuous_fst)
  -- the two sides as integrals over the square
  set Fl : ℝ → ℝ → ℂ := fun s z => (Ioi s).indicator (fun z => f z s) z with hFl
  set Fr : ℝ → ℝ → ℂ := fun s z => {x : ℝ | x ≤ z}.indicator (fun s => f z s) s with hFr
  have hL1 : volterra (kcomp K L) g t = ∫ s in (0 : ℝ)..t, ∫ z in (0 : ℝ)..t, Fl s z := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    simp only [kcomp, hFl]
    rw [← intervalIntegral.integral_mul_const, intervalIntegral.integral_of_le hs.2,
      intervalIntegral.integral_of_le ht, setIntegral_indicator measurableSet_Ioi]
    have e : Ioc 0 t ∩ Ioi s = Ioc s t := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨lt_of_le_of_lt hs.1 h1, h2⟩, h1⟩
    rw [e]
  have hR1 : volterra K (volterra L g) t = ∫ z in (0 : ℝ)..t, ∫ s in (0 : ℝ)..t, Fr s z := by
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [uIcc_of_le ht] at hz
    simp only [volterra, hFr]
    rw [intervalIntegral.integral_indicator hz, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hf]
    ring
  -- integrability on the square
  have hint : IntegrableOn (Function.uncurry Fl) (Set.uIoc 0 t ×ˢ Set.uIoc 0 t) := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := t))).exists_bound_of_continuousOn
      (hfc.continuousOn (s := Icc (0 : ℝ) t ×ˢ Icc 0 t))
    have hmeas : Measurable (Function.uncurry Fl) := by
      have : Function.uncurry Fl = (fun p : ℝ × ℝ => if p.1 < p.2 then f p.2 p.1 else 0) := by
        funext p
        simp only [Function.uncurry, hFl, Set.indicator, Set.mem_Ioi]
      rw [this]
      exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd) hfc.measurable
        measurable_const
    refine Measure.integrableOn_of_bounded (M := M) ?_ hmeas.aestronglyMeasurable ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_ne_top (by simp [Set.uIoc]) (by simp [Set.uIoc])
    · refine ae_restrict_of_forall_mem (measurableSet_uIoc.prod measurableSet_uIoc) fun p hp => ?_
      rw [Set.uIoc_of_le ht] at hp
      have hp' : p ∈ Icc (0 : ℝ) t ×ˢ Icc 0 t :=
        ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩
      simp only [Function.uncurry, hFl, Set.indicator]
      split_ifs
      · exact hM p hp'
      · simp only [norm_zero]
        exact (norm_nonneg _).trans (hM p hp')
  rw [hL1, hR1, intervalIntegral_intervalIntegral_swap hint]
  refine intervalIntegral.integral_congr fun z _ => ?_
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume z] with s hs _
  simp only [hFl, hFr, Set.indicator, Set.mem_Ioi, Set.mem_ofPred_eq]
  by_cases h : s < z
  · simp [h, h.le]
  · have : ¬ s ≤ z := fun h' => h (lt_of_le_of_ne h' hs)
    simp [h, this]

theorem continuous_volterra {K : ℝ → ℝ → ℂ} (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    {g : ℝ → ℂ} (hg : Continuous g) : Continuous (volterra K g) := by
  unfold volterra
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun t s => K t s * g s) (hK.mul (hg.comp continuous_snd)) continuous_id

theorem volterra_congr (K : ℝ → ℝ → ℂ) {g g' : ℝ → ℂ} (h : ∀ s ∈ Icc (0 : ℝ) 1, g s = g' s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : volterra K g t = volterra K g' t := by
  unfold volterra
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  rw [h s ⟨hs.1, hs.2.trans ht.2⟩]

end Volterra

section Def

variable {V : Type} (σ : ℕ → V) (ε : ℕ → ℤ)

/-- **The time integral of a regular chain** (DH21 (newexp2)), in continuation-passing form over a
Catalan code: pairs `q, q+1, …`; `F j` is the coefficient attached to pair `j`; `g` is the
integrand at the last time. -/
@[expose] noncomputable def chainT : LegalCode → ℕ → (ℕ → (V → ℝ) → ℝ → ℝ → ℂ) → (V → ℝ) → ℝ →
    (ℝ → ℂ) → ℂ
  | .nil, _, _, _, t, g => g t
  | .node i r, q, F, α, t, g =>
      ∫ ta in (0 : ℝ)..t, cexp (π * I * (ε q * α (σ q) * ta)) *
        chainT i (q + 1) F α ta (fun t' => ∫ tb in (0 : ℝ)..t',
          cexp (π * I * (-(ε q * α (σ q)) * tb)) * F q α ta tb *
            chainT r (q + i.size + 1) F α tb g)

end Def

section Basic

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ}

theorem chainT_nil (q : ℕ) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (α : V → ℝ) (t : ℝ) (g : ℝ → ℂ) :
    chainT σ ε .nil q F α t g = g t := rfl

theorem chainT_node (i r : LegalCode) (q : ℕ) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (α : V → ℝ) (t : ℝ)
    (g : ℝ → ℂ) : chainT σ ε (.node i r) q F α t g =
      ∫ ta in (0 : ℝ)..t, cexp (π * I * (ε q * α (σ q) * ta)) *
        chainT σ ε i (q + 1) F α ta (fun t' => ∫ tb in (0 : ℝ)..t',
          cexp (π * I * (-(ε q * α (σ q)) * tb)) * F q α ta tb *
            chainT σ ε r (q + i.size + 1) F α tb g) := rfl

/-- `chainT` is homogeneous in the continuation. -/
theorem chainT_const_mul : ∀ (c : LegalCode) (q : ℕ) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (α : V → ℝ)
    (t : ℝ) (a : ℂ) (g : ℝ → ℂ),
    chainT σ ε c q F α t (fun t' => a * g t') = a * chainT σ ε c q F α t g
  | .nil, _, _, _, _, _, _ => rfl
  | .node i r, q, F, α, t, a, g => by
    rw [chainT_node, chainT_node, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ta _ => ?_
    have e : (fun t' => ∫ tb in (0 : ℝ)..t', cexp (π * I * (-(ε q * α (σ q)) * tb)) * F q α ta tb *
        chainT σ ε r (q + i.size + 1) F α tb (fun t' => a * g t')) =
        fun t' => a * ∫ tb in (0 : ℝ)..t', cexp (π * I * (-(ε q * α (σ q)) * tb)) * F q α ta tb *
          chainT σ ε r (q + i.size + 1) F α tb g := by
      funext t'
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun tb _ => ?_
      rw [chainT_const_mul r]
      ring
    rw [e, chainT_const_mul i]
    ring

/-- `chainT` at `t ∈ [0,1]` only sees the continuation and the coefficients on `[0,1]`. -/
theorem chainT_congr : ∀ (c : LegalCode) (q : ℕ) {F F' : ℕ → (V → ℝ) → ℝ → ℝ → ℂ} (α : V → ℝ)
    (_ : ∀ j t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → F j α t s = F' j α t s)
    {g g' : ℝ → ℂ} (_ : ∀ s ∈ Icc (0 : ℝ) 1, g s = g' s) (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1),
    chainT σ ε c q F α t g = chainT σ ε c q F' α t g'
  | .nil, _, _, _, _, _, _, _, hg, t, ht => hg t ht
  | .node i r, q, F, F', α, hF, g, g', hg, t, ht => by
    rw [chainT_node, chainT_node]
    refine intervalIntegral.integral_congr fun ta hta => ?_
    rw [uIcc_of_le ht.1] at hta
    have hta' : ta ∈ Icc (0 : ℝ) 1 := ⟨hta.1, hta.2.trans ht.2⟩
    congr 1
    refine chainT_congr i (q + 1) α hF (fun t' ht' => ?_) ta hta'
    refine intervalIntegral.integral_congr fun tb htb => ?_
    rw [uIcc_of_le ht'.1] at htb
    have htb' : tb ∈ Icc (0 : ℝ) 1 := ⟨htb.1, htb.2.trans ht'.2⟩
    rw [hF q ta tb hta' htb', chainT_congr r (q + i.size + 1) α hF hg tb htb']

/-- **Continuity of the chain integral** in the time and in parameters. -/
theorem continuous_chainT : ∀ (c : LegalCode) (q : ℕ) {X : Type} [TopologicalSpace X]
    {F : X → ℕ → (V → ℝ) → ℝ → ℝ → ℂ} (α : V → ℝ)
    (_ : ∀ j, Continuous fun p : X × (ℝ × ℝ) => F p.1 j α p.2.1 p.2.2)
    {E : X → ℝ → ℂ} (_ : Continuous fun p : X × ℝ => E p.1 p.2),
    Continuous fun p : X × ℝ => chainT σ ε c q (F p.1) α p.2 (E p.1)
  | .nil, _, _, _, _, _, _, _, hE => hE
  | .node i r, q, X, _, F, α, hF, E, hE => by
    simp_rw [chainT_node]
    -- the rest of the chain
    have hR := continuous_chainT r (q + i.size + 1) α hF hE
    -- the continuation of the inner block, a function of `((x, ta), t')`
    have hE' : Continuous fun p : (X × ℝ) × ℝ => ∫ tb in (0 : ℝ)..p.2,
        cexp (π * I * (-(ε q * α (σ q)) * tb)) * F p.1.1 q α p.1.2 tb *
          chainT σ ε r (q + i.size + 1) (F p.1.1) α tb (E p.1.1) := by
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : (X × ℝ) × ℝ) (tb : ℝ) => cexp (π * I * (-(ε q * α (σ q)) * tb)) *
          F p.1.1 q α p.1.2 tb * chainT σ ε r (q + i.size + 1) (F p.1.1) α tb (E p.1.1)) ?_
        continuous_snd
      refine ((by fun_prop : Continuous fun p : ((X × ℝ) × ℝ) × ℝ =>
        cexp (π * I * (-(ε q * α (σ q)) * p.2))).mul ((hF q).comp
          (f := fun p : ((X × ℝ) × ℝ) × ℝ => (p.1.1.1, (p.1.1.2, p.2))) (by fun_prop))).mul ?_
      exact hR.comp (f := fun p : ((X × ℝ) × ℝ) × ℝ => (p.1.1.1, p.2)) (by fun_prop)
    have hI := continuous_chainT i (q + 1) (X := X × ℝ) (F := fun x => F x.1) α
      (fun j => (hF j).comp (f := fun p : (X × ℝ) × (ℝ × ℝ) => (p.1.1, p.2)) (by fun_prop))
      (E := fun (x : X × ℝ) (t' : ℝ) => ∫ tb in (0 : ℝ)..t',
        cexp (π * I * (-(ε q * α (σ q)) * tb)) * F x.1 q α x.2 tb *
          chainT σ ε r (q + i.size + 1) (F x.1) α tb (E x.1)) hE'
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : X × ℝ) (ta : ℝ) => cexp (π * I * (ε q * α (σ q) * ta)) *
        chainT σ ε i (q + 1) (F p.1) α ta (fun t' => ∫ tb in (0 : ℝ)..t',
          cexp (π * I * (-(ε q * α (σ q)) * tb)) * F p.1 q α ta tb *
            chainT σ ε r (q + i.size + 1) (F p.1) α tb (E p.1))) ?_ continuous_snd
    refine (by fun_prop : Continuous fun p : (X × ℝ) × ℝ =>
      cexp (π * I * (ε q * α (σ q) * p.2))).mul ?_
    exact hI.comp (f := fun p : (X × ℝ) × ℝ => ((p.1.1, p.2), p.2)) (by fun_prop)

/-- **The chain integral is bounded** by `B_F^m sup |g|` on `[0,1]`. -/
theorem norm_chainT_le : ∀ (c : LegalCode) (q : ℕ) {F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ} (α : V → ℝ)
    {BF : ℝ} (_ : 0 ≤ BF) (_ : ∀ j t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 → ‖F j α t s‖ ≤ BF)
    {g : ℝ → ℂ} {B : ℝ} (_ : 0 ≤ B) (_ : ∀ s ∈ Icc (0 : ℝ) 1, ‖g s‖ ≤ B) (t : ℝ)
    (_ : t ∈ Icc (0 : ℝ) 1), ‖chainT σ ε c q F α t g‖ ≤ BF ^ c.size * B
  | .nil, _, _, _, _, _, _, _, _, _, hg, t, ht => by
    rw [chainT_nil]
    simpa [LegalCode.size] using hg t ht
  | .node i r, q, F, α, BF, hBF, hF, g, B, hB, hg, t, ht => by
    rw [chainT_node]
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    have hnorm1 : ∀ x : ℝ, ‖cexp (π * I * (x : ℂ))‖ = 1 := fun x => by
      rw [Complex.norm_exp]; simp
    -- the inner continuation
    have hh : ∀ ta ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, ‖∫ tb in (0 : ℝ)..t',
        cexp (π * I * (-(ε q * α (σ q)) * tb)) * F q α ta tb *
          chainT σ ε r (q + i.size + 1) F α tb g‖ ≤ BF * (BF ^ r.size * B) := by
      intro ta hta t' ht'
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := BF * (BF ^ r.size * B))
        fun tb htb => ?_).trans ?_
      · rw [Set.uIoc_of_le ht'.1] at htb
        have htb' : tb ∈ Icc (0 : ℝ) 1 := ⟨htb.1.le, htb.2.trans ht'.2⟩
        rw [norm_mul, norm_mul]
        have := hnorm1 (-(ε q * α (σ q)) * tb)
        push_cast at this
        rw [this, one_mul]
        exact mul_le_mul (hF q ta tb hta htb') (norm_chainT_le r _ α hBF hF hB hg tb htb')
          (norm_nonneg _) hBF
      · rw [sub_zero, abs_of_nonneg ht'.1]
        have : 0 ≤ BF * (BF ^ r.size * B) := by positivity
        nlinarith [ht'.2]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := BF ^ i.size * (BF * (BF ^ r.size * B))) fun ta hta => ?_).trans ?_
    · rw [Set.uIoc_of_le ht.1] at hta
      have hta' : ta ∈ Icc (0 : ℝ) 1 := ⟨hta.1.le, hta.2.trans ht.2⟩
      rw [norm_mul]
      have := hnorm1 (ε q * α (σ q) * ta)
      push_cast at this
      rw [this, one_mul]
      exact norm_chainT_le i _ α hBF hF (by positivity) (hh ta hta') ta hta'
    · rw [sub_zero, abs_of_nonneg ht.1, hsz, pow_add, pow_add, pow_one]
      have : 0 ≤ BF ^ i.size * (BF * (BF ^ r.size * B)) := by positivity
      calc BF ^ i.size * (BF * (BF ^ r.size * B)) * t ≤ BF ^ i.size * (BF * (BF ^ r.size * B)) * 1 :=
            mul_le_mul_of_nonneg_left ht.2 this
        _ = _ := by ring


end Basic

section Exp

variable {V : Type} {σ : ℕ → V} {ε : ℕ → ℤ}

theorem continuous_pchain {P : Type*} (μf : ℕ → P → ℝ) (p : P) (α : V → ℝ) :
    ∀ (c : LegalCode) (q : ℕ), Continuous fun x : ℝ × ℝ => pchain σ ε μf c q p α x.1 x.2
  | .nil, _ => continuous_const
  | .node .nil .nil, q => continuous_sw0 q p α
  | .node .nil (.node a b), q =>
      continuous_kcomp (continuous_sw0 q p α) (continuous_pchain μf p α (.node a b) (q + 1))
  | .node (.node a b) .nil, q =>
      continuous_sandw (continuous_pchain μf p α (.node a b) (q + 1))
  | .node (.node a b) (.node c d), q =>
      continuous_kcomp (continuous_sandw (continuous_pchain μf p α (.node a b) (q + 1)))
        (continuous_pchain μf p α (.node c d) (q + (LegalCode.node a b).size + 1))

theorem cexp_mul_cexp (x y : ℂ) : cexp (π * I * x) * cexp (π * I * y) = cexp (π * I * (x + y)) := by
  rw [← Complex.exp_add]; ring_nf

/-- **One pair with an exponential coefficient** is the sandwich `I_a (·) I_b` with
`a = ε_qα_q + λ_{q,1}` and `b = λ_{q,2} - ε_qα_q`. -/
theorem chainT_node_exp (i r : LegalCode) (q : ℕ) (lam : ℕ → ℝ × ℝ) (α : V → ℝ) {a b : ℝ}
    (ha : a = ε q * α (σ q) + (lam q).1) (hb : b = (lam q).2 - ε q * α (σ q)) (t : ℝ)
    (g : ℝ → ℂ) :
    chainT σ ε (.node i r) q (fun j _ => e2 (lam j)) α t g =
      volterra (iker a) (fun ta => chainT σ ε i (q + 1) (fun j _ => e2 (lam j)) α ta
        (volterra (iker b) (fun tb =>
          chainT σ ε r (q + i.size + 1) (fun j _ => e2 (lam j)) α tb g))) t := by
  rw [chainT_node]
  unfold volterra
  refine intervalIntegral.integral_congr fun ta _ => ?_
  have e : (fun t' => ∫ tb in (0 : ℝ)..t', cexp (π * I * (-(ε q * α (σ q)) * tb)) *
      e2 (lam q) ta tb * chainT σ ε r (q + i.size + 1) (fun j _ => e2 (lam j)) α tb g) =
      fun t' => cexp (π * I * ((lam q).1 * ta)) * ∫ tb in (0 : ℝ)..t', iker b t' tb *
        chainT σ ε r (q + i.size + 1) (fun j _ => e2 (lam j)) α tb g := by
    funext t'
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun tb _ => ?_
    simp only [e2_split, iker, hb]
    have : cexp (π * I * (-(ε q * α (σ q)) * tb)) * cexp (π * I * ((lam q).2 * tb)) =
        cexp (π * I * (((lam q).2 - ε q * α (σ q) : ℝ) * tb)) := by
      rw [cexp_mul_cexp]; congr 2; push_cast; ring
    rw [← this]
    ring
  rw [e, chainT_const_mul, ← mul_assoc]
  congr 1
  simp only [iker, ha]
  rw [cexp_mul_cexp]
  congr 2
  push_cast
  ring

/-- **DH21 (kusingI), (translationk)**: with exponential pair coefficients
`F_j(t_a, t_b) = e^{πi(λ_{j,1}t_a + λ_{j,2}t_b)}`, the chain integral is the Volterra operator of the
pure chain `pchain` in the translated variables `α̃_j = α_j + ε_jλ_{j,1}` with
`μ_j = λ_{j,1} + λ_{j,2}`, on `[0, 1]`. -/
theorem chainT_exp (hε : ∀ j, ε j = 1 ∨ ε j = -1) {P : Type*} (μf : ℕ → P → ℝ) (p : P)
    (lam : ℕ → ℝ × ℝ) {α α' : V → ℝ} :
    ∀ (c : LegalCode) (q : ℕ), c ≠ .nil →
      (∀ j ∈ Set.Ico q (q + c.size), α' (σ j) = α (σ j) + ε j * (lam j).1) →
      (∀ j ∈ Set.Ico q (q + c.size), μf j p = (lam j).1 + (lam j).2) →
      ∀ {g : ℝ → ℂ}, Continuous g → ∀ t ∈ Icc (0 : ℝ) 1,
        chainT σ ε c q (fun j _ => e2 (lam j)) α t g = volterra (pchain σ ε μf c q p α') g t
  | .nil, _, h, _, _, _, _, _, _ => absurd rfl h
  | .node i r, q, _, hα, hμ, g, hg, t, ht => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    have hq : q ∈ Set.Ico q (q + (LegalCode.node i r).size) := by
      simp only [Set.mem_Ico]; omega
    have hεq : (ε q : ℝ) * ε q = 1 := by rcases hε q with h | h <;> simp [h]
    set a := ε q * α' (σ q) with ha'
    set b := μf q p - ε q * α' (σ q) with hb'
    have ha : a = ε q * α (σ q) + (lam q).1 := by
      rw [ha', hα q hq]
      linear_combination (lam q).1 * hεq
    have hb : b = (lam q).2 - ε q * α (σ q) := by
      rw [hb', hα q hq, hμ q hq]
      linear_combination (-(lam q).1) * hεq
    rw [chainT_node_exp i r q lam α ha hb t g]
    have hia : ∀ j ∈ Set.Ico (q + 1) (q + 1 + i.size), α' (σ j) = α (σ j) + ε j * (lam j).1 :=
      fun j hj => hα j (by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hiμ : ∀ j ∈ Set.Ico (q + 1) (q + 1 + i.size), μf j p = (lam j).1 + (lam j).2 :=
      fun j hj => hμ j (by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hra : ∀ j ∈ Set.Ico (q + i.size + 1) (q + i.size + 1 + r.size),
        α' (σ j) = α (σ j) + ε j * (lam j).1 :=
      fun j hj => hα j (by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hrμ : ∀ j ∈ Set.Ico (q + i.size + 1) (q + i.size + 1 + r.size),
        μf j p = (lam j).1 + (lam j).2 :=
      fun j hj => hμ j (by simp only [Set.mem_Ico] at hj ⊢; omega)
    have hia' := continuous_iker a
    have hib' := continuous_iker b
    cases i with
    | nil =>
      cases r with
      | nil =>
        show volterra (iker a) (fun ta => volterra (iker b) g ta) t =
          volterra (kcomp (iker a) (iker b)) g t
        rw [volterra_kcomp hia' hib' hg ht.1]
      | node c d =>
        have hR := chainT_exp hε μf p lam (.node c d) (q + 1) (by simp) hra hrμ hg
        have hPr := continuous_pchain (σ := σ) (ε := ε) μf p α' (.node c d) (q + 1)
        show volterra (iker a) (fun ta => volterra (iker b) (fun tb =>
            chainT σ ε (.node c d) (q + 0 + 1) (fun j _ => e2 (lam j)) α tb g) ta) t =
          volterra (kcomp (kcomp (iker a) (iker b)) (pchain σ ε μf (.node c d) (q + 1) p α')) g t
        rw [volterra_kcomp (continuous_kcomp hia' hib') hPr hg ht.1,
          volterra_kcomp hia' hib' (continuous_volterra hPr hg) ht.1]
        refine volterra_congr _ (fun s hs => ?_) ht
        exact volterra_congr _ (fun u hu => hR u hu) hs
    | node a' b'' =>
      have hIi := continuous_pchain (σ := σ) (ε := ε) μf p α' (.node a' b'') (q + 1)
      cases r with
      | nil =>
        have hI := chainT_exp hε μf p lam (.node a' b'') (q + 1) (by simp) hia hiμ
          (continuous_volterra hib' hg)
        show volterra (iker a) (fun ta => chainT σ ε (.node a' b'') (q + 1) (fun j _ => e2 (lam j)) α ta
            (volterra (iker b) fun tb => g tb)) t =
          volterra (kcomp (kcomp (iker a) (pchain σ ε μf (.node a' b'') (q + 1) p α')) (iker b)) g t
        rw [volterra_kcomp (continuous_kcomp hia' hIi) hib' hg ht.1,
          volterra_kcomp hia' hIi (continuous_volterra hib' hg) ht.1]
        exact volterra_congr _ (fun s hs => hI s hs) ht
      | node c d =>
        have hPr := continuous_pchain (σ := σ) (ε := ε) μf p α' (.node c d)
          (q + (LegalCode.node a' b'').size + 1)
        have hR := chainT_exp hε μf p lam (.node c d) (q + (LegalCode.node a' b'').size + 1)
          (by simp) hra hrμ hg
        have hcv := continuous_volterra hib' (continuous_volterra hPr hg)
        have hI := chainT_exp hε μf p lam (.node a' b'') (q + 1) (by simp) hia hiμ hcv
        show volterra (iker a) (fun ta => chainT σ ε (.node a' b'') (q + 1) (fun j _ => e2 (lam j)) α ta
            (volterra (iker b) fun tb => chainT σ ε (.node c d) (q + (LegalCode.node a' b'').size + 1)
              (fun j _ => e2 (lam j)) α tb g)) t =
          volterra (kcomp (kcomp (kcomp (iker a) (pchain σ ε μf (.node a' b'') (q + 1) p α'))
            (iker b)) (pchain σ ε μf (.node c d) (q + (LegalCode.node a' b'').size + 1) p α')) g t
        rw [volterra_kcomp (continuous_kcomp (continuous_kcomp hia' hIi) hib') hPr hg ht.1,
          volterra_kcomp (continuous_kcomp hia' hIi) hib' (continuous_volterra hPr hg) ht.1,
          volterra_kcomp hia' hIi hcv ht.1]
        refine volterra_congr _ (fun s hs => ?_) ht
        rw [← hI s hs]
        refine chainT_congr _ _ α (fun _ _ _ _ _ => rfl) (fun u hu => ?_) s hs
        exact volterra_congr _ (fun v hv => hR v hv) hu

end Exp

end WaveTurbulence.ClassJR
