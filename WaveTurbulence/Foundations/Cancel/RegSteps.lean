/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.ChainK

/-!
# Products, swaps and the type 2 step of the regularized limits (DH21 (recurtype2))

* `RegLim2.mul`, `RegLim2.swap`, `RegLim2.const`: the invariant is preserved by products, by the
  swap `(t, s) ↦ (s, t)` and holds for constants.
* `chainK_congr`: the regularized chain only sees its kernels on the square and the continuation on
  `[0, 1]`.
* `KFam.ofFinset`: finitely many coefficients with the invariant form a family with uniform bounds,
  after clamping onto the square.
* `regLim2_type2`: the type 2 step. If the pair coefficients of the two chains and the lone pair
  coefficient have the invariant, so does
  `chainK⁺ t (t' ↦ chainK⁻ s (s' ↦ R_lp(t', s')))`. Its limit is the iterated chain limit `chainL`.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-! ### Products and swaps -/

theorem RegLim2.const (a : ℂ) : RegLim2 (fun _ _ _ => a) (fun _ _ => a) := by
  refine ⟨⟨‖a‖, Eventually.of_forall fun _ _ _ _ _ => le_rfl⟩, ⟨0, Eventually.of_forall ?_⟩,
    fun _ _ _ _ => tendsto_const_nhds⟩
  intro θ t _ s _ t' _ s' _; simp

theorem RegLim2.swap {R : ℝ → ℝ → ℝ → ℂ} {J : ℝ → ℝ → ℂ} (h : RegLim2 R J) :
    RegLim2 (fun θ t s => R θ s t) (fun t s => J s t) := by
  obtain ⟨M, hM⟩ := h.bound
  obtain ⟨L, hL⟩ := h.lip
  refine ⟨⟨M, hM.mono fun θ hθ t ht s hs => hθ s hs t ht⟩, ⟨L, hL.mono fun θ hθ t ht s hs t' ht' s' hs' =>
    (hθ s hs t ht s' hs' t' ht').trans_eq (by ring)⟩, fun t ht s hs => h.lim s hs t ht⟩

theorem RegLim2.mul {R₁ R₂ : ℝ → ℝ → ℝ → ℂ} {J₁ J₂ : ℝ → ℝ → ℂ} (h₁ : RegLim2 R₁ J₁)
    (h₂ : RegLim2 R₂ J₂) : RegLim2 (fun θ t s => R₁ θ t s * R₂ θ t s) (fun t s => J₁ t s * J₂ t s) := by
  obtain ⟨M₁, hM₁⟩ := h₁.bound
  obtain ⟨M₂, hM₂⟩ := h₂.bound
  obtain ⟨L₁, hL₁⟩ := h₁.lip
  obtain ⟨L₂, hL₂⟩ := h₂.lip
  refine ⟨⟨max M₁ 0 * max M₂ 0, ?_⟩, ⟨max M₁ 0 * max L₂ 0 + max M₂ 0 * max L₁ 0, ?_⟩,
    fun t ht s hs => (h₁.lim t ht s hs).mul (h₂.lim t ht s hs)⟩
  · filter_upwards [hM₁, hM₂] with θ h1 h2 t ht s hs
    rw [norm_mul]
    exact mul_le_mul ((h1 t ht s hs).trans (le_max_left _ _)) ((h2 t ht s hs).trans (le_max_left _ _))
      (norm_nonneg _) (le_max_right _ _)
  · filter_upwards [hM₁, hM₂, hL₁, hL₂] with θ hm1 hm2 hl1 hl2 t ht s hs t' ht' s' hs'
    have e : R₁ θ t s * R₂ θ t s - R₁ θ t' s' * R₂ θ t' s' =
        R₁ θ t s * (R₂ θ t s - R₂ θ t' s') + (R₁ θ t s - R₁ θ t' s') * R₂ θ t' s' := by ring
    rw [e]
    have hd : 0 ≤ |t - t'| + |s - s'| := by positivity
    calc ‖R₁ θ t s * (R₂ θ t s - R₂ θ t' s') + (R₁ θ t s - R₁ θ t' s') * R₂ θ t' s'‖
        ≤ ‖R₁ θ t s‖ * ‖R₂ θ t s - R₂ θ t' s'‖ + ‖R₁ θ t s - R₁ θ t' s'‖ * ‖R₂ θ t' s'‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ max M₁ 0 * (max L₂ 0 * (|t - t'| + |s - s'|)) +
            max L₁ 0 * (|t - t'| + |s - s'|) * max M₂ 0 := by
          refine add_le_add (mul_le_mul ((hm1 t ht s hs).trans (le_max_left _ _))
            ((hl2 t ht s hs t' ht' s' hs').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd))
            (norm_nonneg _) (le_max_right _ _)) (mul_le_mul ((hl1 t ht s hs t' ht' s' hs').trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)) ((hm2 t' ht' s' hs').trans
            (le_max_left _ _)) (norm_nonneg _) (by positivity))
      _ = (max M₁ 0 * max L₂ 0 + max M₂ 0 * max L₁ 0) * (|t - t'| + |s - s'|) := by ring

theorem RegLim2.prod {ι : Type*} (s : Finset ι) {R : ι → ℝ → ℝ → ℝ → ℂ} {J : ι → ℝ → ℝ → ℂ}
    (h : ∀ i ∈ s, RegLim2 (R i) (J i)) :
    RegLim2 (fun θ t u => ∏ i ∈ s, R i θ t u) (fun t u => ∏ i ∈ s, J i t u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RegLim2.const 1
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ### Congruence and clamping -/

theorem chainK_congr {P P' : ℕ → ℝ → ℝ → ℂ} :
    ∀ (c : LegalCode) (q : ℕ),
      (∀ j, q ≤ j → j < q + c.size → ∀ ta ∈ Icc (0 : ℝ) 1, ∀ tb ∈ Icc (0 : ℝ) 1, P j ta tb = P' j ta tb) →
      ∀ {g g' : ℝ → ℂ}, (∀ x ∈ Icc (0 : ℝ) 1, g x = g' x) → ∀ t ∈ Icc (0 : ℝ) 1,
        chainK P c q t g = chainK P' c q t g'
  | .nil, _, _, _, _, hg, t, ht => hg t ht
  | .node i r, q, hP, g, g', hg, t, ht => by
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    simp only [chainK_node]
    refine intervalIntegral.integral_congr fun ta hta => ?_
    rw [uIcc_of_le ht.1] at hta
    have hta' : ta ∈ Icc (0 : ℝ) 1 := ⟨hta.1, hta.2.trans ht.2⟩
    refine chainK_congr i (q + 1) (fun j h1 h2 => hP j (by omega) (by omega)) (fun x hx => ?_) ta hta'
    refine intervalIntegral.integral_congr fun tb htb => ?_
    rw [uIcc_of_le hx.1] at htb
    have htb' : tb ∈ Icc (0 : ℝ) 1 := ⟨htb.1, htb.2.trans hx.2⟩
    rw [hP q le_rfl (by omega) ta hta' tb htb',
      chainK_congr r _ (fun j h1 h2 => hP j (by omega) (by omega)) hg tb htb']

/-- The clamped coefficients of a finite family form a `KFam`. -/
theorem KFam.ofFinset (s : Finset ℕ) {R : ℕ → ℝ → ℝ → ℝ → ℂ} {R₀ : ℕ → ℝ → ℝ → ℂ}
    (h : ∀ j ∈ s, RegLim2 (R j) (R₀ j)) :
    KFam (fun j θ ta tb => if j ∈ s then R j θ (clamp01 ta) (clamp01 tb) else 0)
      (fun j ta tb => if j ∈ s then R₀ j ta tb else 0) := by
  have hb : ∀ j ∈ s, ∃ M, ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ ta ∈ Icc (0 : ℝ) 1, ∀ tb ∈ Icc (0 : ℝ) 1,
      ‖R j θ ta tb‖ ≤ M := fun j hj => (h j hj).bound
  have hl : ∀ j ∈ s, ∃ L, ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      ∀ t' ∈ Icc (0 : ℝ) 1, ∀ u' ∈ Icc (0 : ℝ) 1, ‖R j θ t u - R j θ t' u'‖ ≤ L * (|t - t'| + |u - u'|) :=
    fun j hj => (h j hj).lip
  choose! M hM using hb
  choose! L hL using hl
  set M' := ∑ j ∈ s, max (M j) 0
  set L' := ∑ j ∈ s, max (L j) 0
  have hMle : ∀ j ∈ s, max (M j) 0 ≤ M' := fun j hj =>
    Finset.single_le_sum (f := fun j => max (M j) 0) (fun _ _ => le_max_right _ _) hj
  have hLle : ∀ j ∈ s, max (L j) 0 ≤ L' := fun j hj =>
    Finset.single_le_sum (f := fun j => max (L j) 0) (fun _ _ => le_max_right _ _) hj
  refine ⟨⟨M', ?_⟩, ⟨L', ?_⟩, fun j ta hta tb htb => ?_⟩
  · filter_upwards [(Filter.eventually_all_finset s).2 hM] with θ hθ j ta tb
    split_ifs with hj
    · exact (hθ j hj _ (clamp01_mem ta) _ (clamp01_mem tb)).trans ((le_max_left _ _).trans (hMle j hj))
    · simp only [norm_zero]; exact Finset.sum_nonneg fun _ _ => le_max_right _ _
  · filter_upwards [(Filter.eventually_all_finset s).2 hL] with θ hθ j ta tb ta' tb'
    split_ifs with hj
    · refine (lip_clamp (le_max_right (L j) 0) (fun t ht u hu t' ht' u' hu' =>
        (hθ j hj t ht u hu t' ht' u' hu').trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (by positivity))) ta tb ta' tb').trans ?_
      exact mul_le_mul_of_nonneg_right (hLle j hj) (by positivity)
    · simp only [sub_self, norm_zero]
      exact mul_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _) (by positivity)
  · split_ifs with hj
    · simpa [clamp01_eq hta, clamp01_eq htb] using (h j hj).lim ta hta tb htb
    · exact tendsto_const_nhds

/-! ### Lipschitz in the time, for any chain -/

theorem chainK_lip' {P : ℕ → ℝ → ℝ → ℂ} {m : ℝ} (hm : 0 ≤ m)
    (hP : ∀ j, ∀ ta ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) 1, ∀ (f : ℝ → ℂ) (G : ℝ),
      (∀ y ∈ Icc (0 : ℝ) x, ‖f y‖ ≤ G) → ‖∫ tb in (0 : ℝ)..x, P j ta tb * f tb‖ ≤ m * max G 0)
    (hPc : ∀ j, Continuous (Function.uncurry (P j))) (c : LegalCode) (q : ℕ) {g : ℝ → ℂ} {G Lg : ℝ}
    (hG : 0 ≤ G) (hLg : 0 ≤ Lg) (hg : ∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ G)
    (hgL : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖g x - g y‖ ≤ Lg * |x - y|) (hgc : Continuous g)
    {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (ht' : t' ∈ Icc (0 : ℝ) 1) :
    ‖chainK P c q t g - chainK P c q t' g‖ ≤ (Lg + m ^ c.size * G) * |t - t'| := by
  cases c with
  | nil =>
    simp only [chainK_nil]
    exact (hgL t ht t' ht').trans (mul_le_mul_of_nonneg_right (by simp; positivity) (abs_nonneg _))
  | node i r =>
    refine (chainK_lip hm hP i r q hG hg hPc hgc ht ht').trans
      (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    have hsz : (LegalCode.node i r).size = i.size + r.size + 1 := rfl
    rw [hsz, pow_add, pow_add, pow_one]
    nlinarith [show 0 ≤ m ^ i.size * m ^ r.size * m * G by positivity]

/-! ### The type 2 step -/

/-- **The type 2 step** (DH21 (newexp2), (recurtype2)). -/
theorem regLim2_type2 {bbp bbm : ℕ → Bool} {Rp Rm : ℕ → ℝ → ℝ → ℝ → ℂ}
    {Rp₀ Rm₀ : ℕ → ℝ → ℝ → ℂ} (hRp : KFam Rp Rp₀) (hRm : KFam Rm Rm₀)
    {Rlp : ℝ → ℝ → ℝ → ℂ} {Jlp : ℝ → ℝ → ℂ} (hlp : KFam (fun _ => Rlp) (fun _ => Jlp))
    (cp cm : LegalCode) :
    RegLim2 (fun θ t s => chainK (kP bbp Rp θ) cp 0 t
        (fun t' => chainK (kP bbm Rm θ) cm 0 s (fun s' => Rlp θ t' s')))
      (fun t s => chainL (kD bbp Rp₀) cp 0 t
        (fun t' => chainL (kD bbm Rm₀) cm 0 s (fun s' => Jlp t' s'))) := by
  obtain ⟨mp, hmp0, hmp⟩ := mass_kP (bb := bbp) hRp
  obtain ⟨mm, hmm0, hmm⟩ := mass_kP (bb := bbm) hRm
  obtain ⟨Ml, hMl⟩ := hlp.bound
  obtain ⟨Ll, hLl⟩ := hlp.lip
  have hRlc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Continuous (Function.uncurry (Rlp θ)) :=
    (hlp.cont).mono fun θ hθ => hθ 0
  set G := max Ml 0 with hGdef
  set Ll' := max Ll 0 with hLl'
  -- the inner chain, as a function of `(t', s)`
  set H : ℝ → ℝ → ℝ → ℂ := fun θ t' s => chainK (kP bbm Rm θ) cm 0 s (fun s' => Rlp θ t' s') with hH
  have hHc : ∀ᶠ θ in 𝓝[>] (0 : ℝ), Continuous (Function.uncurry (H θ)) := by
    filter_upwards [continuous_kP (bb := bbm) hRm, hRlc] with θ hP hR
    exact continuous_chainK hP cm 0 (X := ℝ) (g := fun t' s' => Rlp θ t' s') hR
  have hHb : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t' s, s ∈ Icc (0 : ℝ) 1 → ‖H θ t' s‖ ≤ mm ^ cm.size * G := by
    filter_upwards [hmm, hMl] with θ hθm hθM t' s hs
    exact norm_chainK_le hmm0 hθm cm 0 (le_max_right _ _)
      (fun x _ => (hθM 0 t' x).trans (le_max_left _ _)) s hs
  -- `H` is Lipschitz in `t'` (linearity) and in `s`
  have hHt : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t₁ t₂ s, s ∈ Icc (0 : ℝ) 1 →
      ‖H θ t₁ s - H θ t₂ s‖ ≤ mm ^ cm.size * (Ll' * |t₁ - t₂|) := by
    filter_upwards [hmm, hLl, continuous_kP (bb := bbm) hRm, hRlc] with θ hθm hθL hP hR t₁ t₂ s hs
    have hc₁ : Continuous fun x => Rlp θ t₁ x := hR.comp (continuous_const.prodMk continuous_id)
    have hc₂ : Continuous fun x => Rlp θ t₂ x := hR.comp (continuous_const.prodMk continuous_id)
    simp only [hH]
    rw [chainK_sub hP cm 0 hc₁ hc₂ s]
    have := norm_chainK_le hmm0 hθm cm 0 (by positivity : 0 ≤ Ll' * |t₁ - t₂|)
      (g := fun x => Rlp θ t₁ x - Rlp θ t₂ x) (fun x _ => by
        have := hθL 0 t₁ x t₂ x
        simp only [sub_self, abs_zero, add_zero] at this
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) s hs
    exact this
  have hHs : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ t' s₁ s₂, s₁ ∈ Icc (0 : ℝ) 1 → s₂ ∈ Icc (0 : ℝ) 1 →
      ‖H θ t' s₁ - H θ t' s₂‖ ≤ (Ll' + mm ^ cm.size * G) * |s₁ - s₂| := by
    filter_upwards [hmm, hLl, hMl, continuous_kP (bb := bbm) hRm, hRlc] with θ hθm hθL hθM hP hR
      t' s₁ s₂ hs₁ hs₂
    exact chainK_lip' hmm0 hθm hP cm 0 (le_max_right _ _) (le_max_right _ _)
      (fun x _ => (hθM 0 t' x).trans (le_max_left _ _))
      (fun x _ y _ => by
        have := hθL 0 t' x t' y
        simp only [sub_self, abs_zero, zero_add] at this
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
      (hR.comp (continuous_const.prodMk continuous_id)) hs₁ hs₂
  set B := mm ^ cm.size * G with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨⟨mp ^ cp.size * B, ?_⟩, ⟨max (Ll' * mm ^ cm.size + mp ^ cp.size * B)
      (mp ^ cp.size * (Ll' + B)), ?_⟩, ?_⟩
  · -- the bound
    filter_upwards [hmp, hHb] with θ hθm hθH t ht s hs
    exact norm_chainK_le hmp0 hθm cp 0 hB0 (fun x _ => hθH x s hs) t ht
  · -- the Lipschitz bound
    filter_upwards [hmp, hHb, hHt, hHs, hHc, continuous_kP (bb := bbp) hRp] with θ hθm hθH hθt hθs hθc hP
      t ht s hs t' ht' s' hs'
    have hcs : ∀ s, Continuous fun t' => H θ t' s := fun s =>
      hθc.comp (continuous_id.prodMk continuous_const)
    -- in `t`
    have h1 : ‖chainK (kP bbp Rp θ) cp 0 t (fun x => H θ x s) -
        chainK (kP bbp Rp θ) cp 0 t' (fun x => H θ x s)‖ ≤
          (Ll' * mm ^ cm.size + mp ^ cp.size * B) * |t - t'| :=
      chainK_lip' hmp0 hθm hP cp 0 hB0 (by positivity) (fun x _ => hθH x s hs)
        (fun x _ y _ => (hθt x y s hs).trans_eq (by ring)) (hcs s) ht ht'
    -- in `s`
    have h2 : ‖chainK (kP bbp Rp θ) cp 0 t' (fun x => H θ x s) -
        chainK (kP bbp Rp θ) cp 0 t' (fun x => H θ x s')‖ ≤
          mp ^ cp.size * ((Ll' + B) * |s - s'|) := by
      rw [chainK_sub hP cp 0 (hcs s) (hcs s') t']
      exact norm_chainK_le hmp0 hθm cp 0 (by positivity) (fun x _ => hθs x s s' hs hs') t' ht'
    show ‖chainK (kP bbp Rp θ) cp 0 t (fun x => H θ x s) -
      chainK (kP bbp Rp θ) cp 0 t' (fun x => H θ x s')‖ ≤ _
    calc _ ≤ ‖chainK (kP bbp Rp θ) cp 0 t (fun x => H θ x s) -
            chainK (kP bbp Rp θ) cp 0 t' (fun x => H θ x s)‖ +
          ‖chainK (kP bbp Rp θ) cp 0 t' (fun x => H θ x s) -
            chainK (kP bbp Rp θ) cp 0 t' (fun x => H θ x s')‖ := by
          rw [← sub_add_sub_cancel _ (chainK (kP bbp Rp θ) cp 0 t' (fun x => H θ x s))]
          exact norm_add_le _ _
      _ ≤ (Ll' * mm ^ cm.size + mp ^ cp.size * B) * |t - t'| +
          mp ^ cp.size * ((Ll' + B) * |s - s'|) := add_le_add h1 h2
      _ ≤ _ := by
          have ha := le_max_left (Ll' * mm ^ cm.size + mp ^ cp.size * B) (mp ^ cp.size * (Ll' + B))
          have hb := le_max_right (Ll' * mm ^ cm.size + mp ^ cp.size * B) (mp ^ cp.size * (Ll' + B))
          have h3 : 0 ≤ |t - t'| := abs_nonneg _
          have h4 : 0 ≤ |s - s'| := abs_nonneg _
          nlinarith
  · -- the limit
    intro t ht s hs
    have hin : ∀ t' ∈ Icc (0 : ℝ) 1, Tendsto (fun θ => H θ t' s) (𝓝[>] 0)
        (𝓝 (chainL (kD bbm Rm₀) cm 0 s (fun s' => Jlp t' s'))) := fun t' ht' =>
      tendsto_chainK hRm cm 0 (g := fun θ s' => Rlp θ t' s') (G := G)
        (hRlc.mono fun θ hθ => hθ.comp (continuous_const.prodMk continuous_id))
        (hMl.mono fun θ hθ x _ => (hθ 0 t' x).trans (le_max_left _ _)) s hs
        (fun x hx => hlp.lim 0 t' ht' x ⟨hx.1, hx.2.le.trans hs.2⟩) (fun _ => hlp.lim 0 t' ht' s hs)
    exact tendsto_chainK hRp cp 0 (g := fun θ t' => H θ t' s) (G := B)
      (hHc.mono fun θ hθ => hθ.comp (continuous_id.prodMk continuous_const))
      (hHb.mono fun θ hθ x _ => hθ x s hs) t ht
      (fun x hx => hin x ⟨hx.1, hx.2.le.trans ht.2⟩) (fun _ => hin t ht)

end WaveTurbulence.Cancel
