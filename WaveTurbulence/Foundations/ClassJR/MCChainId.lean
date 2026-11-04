/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.MCChain1

/-!
# The expansion identity of a chain with a bottom coefficient

DH21 L1121–L1145. Let `c` be a chain with pair coefficients `R_j = ∫ 𝒞_j e2` and bottom coefficient
`G = ∫ 𝒞_b e2`. Fixing the frequencies `z` of the pairs and `λ` of the bottom, the chain integral
with exponential pair coefficients is the Volterra operator of `pchain` at the shifted variables
`α̃_j = α_j + ε_jλ_{j,1}` (`chainT_exp`). Lemma 5.10 expands it over `Y ⊆ adj`, Lemma G turns each
`Ĩ_Y` into a class `J` piece plus a class `R` piece, and
`Φ(ε_jα̃_j) = Φ(ε_jα_j) + (Φ(ε_jα_j + λ_{j,1}) - Φ(ε_jα_j))` (DH21 L1141–L1145) expands the
product over `Y' ⊆ Y` (`chainT_exp_expand`). Integrating (`chainT_bottom_expand`):
`chainT c R α t (G α · s) = Σ_{Y ⊆ adj} Σ_{Y' ⊆ Y} ∏_{j∈Y'} Φ(ζ_{σ j}α_{σ j}) (∫ g_J + ∫ g_R)`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

section Expand

variable {V : Type} [DecidableEq V] {σ : ℕ → V} {ε : ℕ → ℤ}

/-- The parameters `μ_j = λ_{j,1} + λ_{j,2}` of the chain kernels. -/
@[expose] def μZ (c : LegalCode) (j : ℕ) (z : ZT c) : ℝ := (Λz c 0 z j).1 + (Λz c 0 z j).2

theorem measurable_μZ (c : LegalCode) (j : ℕ) : Measurable (μZ c j) := by
  unfold μZ
  exact ((continuous_Λz c 0 j).fst.add (continuous_Λz c 0 j).snd).measurable

theorem volterra_const_mul (a : ℂ) (K : ℝ → ℝ → ℂ) (g : ℝ → ℂ) (t : ℝ) :
    volterra (fun t s => a * K t s) g t = a * volterra K g t := by
  unfold volterra
  simp_rw [mul_assoc]
  exact intervalIntegral.integral_const_mul a _

/-- **The pointwise expansion of an exponential chain** (DH21 (kusingI), Lemma 5.10, Lemma G and
L1141–L1145). -/
theorem chainT_exp_expand (hε : ∀ j, ε j = 1 ∨ ε j = -1) {ζ : V → ℤ}
    {c : LegalCode} (hζ : ∀ j ∈ Set.Ico 0 c.size, ζ (σ j) = ε j) (hc : c ≠ .nil)
    (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {GJ GR : Finset ℕ → ZT c → ℝ → (V → ℝ) → ℝ → ℂ}
    (hG : ∀ Y ∈ (adjSet c 0).powerset, ∀ z (L0 : ℝ) α, ∀ t ∈ Icc (0 : ℝ) 1,
      volterra (tildeP σ ε (μZ c) Y c 0 z α) (fun s => cexp (π * I * (L0 * s))) t =
        GJ Y z L0 α t + GR Y z L0 α t)
    (α : V → ℝ) (z : ZT c) (L0 : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    chainT σ ε c 0 (fun j _ => e2 (Λz c 0 z j)) α t (fun s => cexp (π * I * (L0 * s))) =
      ∑ Y ∈ (adjSet c 0).powerset, ∑ Y' ∈ Y.powerset,
        (∏ j ∈ Y', PhiZ ζ (σ j) (α (σ j))) *
          ((∏ j ∈ Y \ Y', Dfun (ε j) (Λz c 0 z j).1 (α (σ j))) *
            (GJ Y z L0 (shiftV σ ε (Λz c 0 z) 0 c.size α) t +
              GR Y z L0 (shiftV σ ε (Λz c 0 z) 0 c.size α) t)) := by
  have hinj0 : Set.InjOn σ (Set.Ico 0 (0 + c.size)) := by rwa [zero_add]
  set α' := shiftV σ ε (Λz c 0 z) 0 c.size α with hα'
  have hα : ∀ j ∈ Set.Ico 0 (0 + c.size), α' (σ j) = α (σ j) + ε j * (Λz c 0 z j).1 :=
    fun j hj => shiftV_apply (Λz c 0 z) hinj0 α hj
  rw [chainT_exp hε (μZ c) z (Λz c 0 z) c 0 hc hα (fun j _ => rfl) (continuous_cexp_L0 L0) t ht]
  have e : pchain σ ε (μZ c) c 0 z α' = fun t s => ∑ Y ∈ (adjSet c 0).powerset,
      (∏ j ∈ Y, phiQ σ ε j α') * tildeP σ ε (μZ c) Y c 0 z α' t s := by
    funext t s
    exact pchain_expand z α' c 0 t s
  rw [e, volterra_finsum (adjSet c 0).powerset
    (fun Y t s => (∏ j ∈ Y, phiQ σ ε j α') * tildeP σ ε (μZ c) Y c 0 z α' t s)
    (fun Y => continuous_const.mul (continuous_tildeP Y z α' c 0)) (continuous_cexp_L0 L0) t]
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [volterra_const_mul, hG Y hY z L0 α' t ht]
  have hphi : ∀ j ∈ Y, phiQ σ ε j α' =
      PhiZ ζ (σ j) (α (σ j)) + Dfun (ε j) (Λz c 0 z j).1 (α (σ j)) := by
    intro j hj
    have hjr : j ∈ Set.Ico 0 (0 + c.size) := by
      have := mem_adjSet c 0 j (Finset.mem_powerset.1 hY hj)
      simp only [Set.mem_Ico]; omega
    have hj' : j ∈ Set.Ico 0 c.size := by rwa [zero_add] at hjr
    have h1 : (ε j : ℝ) * (α (σ j) + ε j * (Λz c 0 z j).1) =
        ε j * α (σ j) + (Λz c 0 z j).1 := by
      rcases hε j with h | h
      · simp [h]
      · simp [h]; ring
    simp only [phiQ, PhiZ, Dfun]
    rw [hα j hjr, h1, hζ j hj']
    ring
  rw [Finset.prod_congr rfl hphi, Finset.prod_add, Finset.sum_mul]
  exact Finset.sum_congr rfl fun Y' _ => by ring

end Expand

section Sums

/-- Integrals of double finite sums of integrable functions. -/
theorem integral_sum2 {X κ : Type*} [MeasurableSpace X] {μ : Measure X} (s : Finset κ)
    (t : κ → Finset κ) (a : κ → κ → ℂ) (f g : κ → κ → X → ℂ)
    (hf : ∀ i ∈ s, ∀ k ∈ t i, Integrable (f i k) μ ∧ Integrable (g i k) μ) :
    ∫ x, ∑ i ∈ s, ∑ k ∈ t i, a i k * (f i k x + g i k x) ∂μ =
      ∑ i ∈ s, ∑ k ∈ t i, a i k * (∫ x, f i k x ∂μ + ∫ x, g i k x ∂μ) := by
  have hI : ∀ i ∈ s, ∀ k ∈ t i, Integrable (fun x => a i k * (f i k x + g i k x)) μ :=
    fun i hi k hk => ((hf i hi k hk).1.add (hf i hi k hk).2).const_mul (a i k)
  rw [integral_finsetSum s fun i hi => integrable_finsetSum (t i) fun k hk => hI i hi k hk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum (t i) fun k hk => hI i hi k hk]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_const_mul, integral_add (hf i hi k hk).1 (hf i hi k hk).2]

end Sums

section Bottom

variable {V : Type} [DecidableEq V] (σ : ℕ → V) (ε : ℕ → ℤ)

/-- **The integrand of a chain term** on the pair and bottom frequencies `w = (z, λ)`:
`∏_j 𝒞_j(λ_j) · 𝒞_b(λ) e^{πiλ₂s} · ∏_{j ∈ Y∖Y'} D_j · G_Y(z, λ₁; α̃, t)`. -/
@[expose] noncomputable def gTerm (P : ℕ → PSym V) {ιb : Type} (fb : ιb → V)
    (Cb : (ιb → ℝ) → ℝ × ℝ → ℂ) (c : LegalCode) (Gp : ZT c → ℝ → (V → ℝ) → ℝ → ℂ)
    (Y Y' : Finset ℕ) (α : V → ℝ) (t s : ℝ) (w : ZT c × (ℝ × ℝ)) : ℂ :=
  Mz (fun j => (P j).C (α ∘ (P j).f)) c 0 w.1 *
    (Cb (α ∘ fb) w.2 * cexp (π * I * (w.2.2 * s)) *
      ((∏ j ∈ Y \ Y', Dfun (ε j) (Λz c 0 w.1 j).1 (α (σ j))) *
        Gp w.1 w.2.1 (shiftV σ ε (Λz c 0 w.1) 0 c.size α) t))

variable {σ ε}

/-- **The expansion of a chain with a bottom coefficient** (DH21 L1121–L1145). -/
theorem chainT_bottom_expand (hε : ∀ j, ε j = 1 ∨ ε j = -1) {ζ : V → ℤ} {c : LegalCode}
    (hζ : ∀ j ∈ Set.Ico 0 c.size, ζ (σ j) = ε j) (hc : c ≠ .nil)
    (hinj : Set.InjOn σ (Set.Ico 0 c.size))
    {P : ℕ → PSym V} (hP : ∀ j, SymReg (P j).C) {R : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (hR : ∀ j ∈ Set.Ico 0 c.size, ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      R j α t s = ∫ lam, (P j).C (α ∘ (P j).f) lam * e2 lam t s)
    {ιb : Type} [Fintype ιb] {fb : ιb → V} {Cb : (ιb → ℝ) → ℝ × ℝ → ℂ} (hCb : SymReg Cb)
    {G : (V → ℝ) → ℝ → ℝ → ℂ}
    (hG : ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      G α t s = ∫ lam, Cb (α ∘ fb) lam * e2 lam t s)
    {GJ GR : Finset ℕ → ZT c → ℝ → (V → ℝ) → ℝ → ℂ}
    (hGJR : ∀ Y ∈ (adjSet c 0).powerset, ∀ z (L0 : ℝ) α, ∀ t ∈ Icc (0 : ℝ) 1,
      volterra (tildeP σ ε (μZ c) Y c 0 z α) (fun s => cexp (π * I * (L0 * s))) t =
        GJ Y z L0 α t + GR Y z L0 α t)
    (α : V → ℝ) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hint : ∀ Y ∈ (adjSet c 0).powerset, ∀ Y' ∈ Y.powerset,
      Integrable (gTerm σ ε P fb Cb c (GJ Y) Y Y' α t s) ∧
        Integrable (gTerm σ ε P fb Cb c (GR Y) Y Y' α t s)) :
    chainT σ ε c 0 R α t (fun t' => G α t' s) =
      ∑ Y ∈ (adjSet c 0).powerset, ∑ Y' ∈ Y.powerset, (∏ j ∈ Y', PhiZ ζ (σ j) (α (σ j))) *
        ((∫ w, gTerm σ ε P fb Cb c (GJ Y) Y Y' α t s w) +
          ∫ w, gTerm σ ε P fb Cb c (GR Y) Y Y' α t s w) := by
  classical
  have hinj0 : Set.InjOn σ (Set.Ico 0 (0 + c.size)) := by rwa [zero_add]
  set Ĉ : ℕ → ℝ × ℝ → ℂ := fun j => (P j).C (α ∘ (P j).f) with hĈ_def
  have hĈ : ∀ j, Integrable (Ĉ j) := fun j => (hP j).integrable _
  set R'' : ℕ → (V → ℝ) → ℝ → ℝ → ℂ :=
    fun j β t s => ∫ lam, (P j).C (β ∘ (P j).f) lam * e2 lam t s with hR''
  set R3 : ℕ → (V → ℝ) → ℝ → ℝ → ℂ := fun j => if j ∈ Set.Ico 0 c.size then R'' j else R j
    with hR3
  set φ : ℝ × ℝ → ℂ := fun lam => Cb (α ∘ fb) lam * cexp (π * I * (lam.2 * s)) with hφ_def
  set E : ℝ × ℝ → ℝ → ℂ := fun lam t' => cexp (π * I * (lam.1 * t')) with hE_def
  have hn : ∀ x : ℝ, ‖cexp (π * I * x)‖ = 1 := fun x => by rw [Complex.norm_exp]; simp
  have hφ : Integrable φ := by
    refine (hCb.integrable (α ∘ fb)).mul_bdd (c := 1) (by fun_prop)
      (Eventually.of_forall fun lam => ?_)
    have := hn (lam.2 * s)
    push_cast at this
    rw [this]
  have hEc : Continuous (Function.uncurry E) := by simp only [hE_def]; fun_prop
  have hEB : ∀ lam, ∀ t' ∈ Icc (0 : ℝ) 1, ‖E lam t'‖ ≤ 1 := fun lam t' _ => by
    have := hn (lam.1 * t'); push_cast at this; simp only [hE_def, this, le_refl]
  have hG'' : (fun t' => ∫ lam, φ lam * E lam t') =
      fun t' => ∫ lam, Cb (α ∘ fb) lam * e2 lam t' s := by
    funext t'
    refine integral_congr_ae (Eventually.of_forall fun lam => ?_)
    simp only [hφ_def, hE_def, e2_split]
    ring
  have hGc : Continuous fun t' => ∫ lam, φ lam * E lam t' := by
    rw [hG'']
    exact (continuous_e2_rep (hCb.integrable (α ∘ fb))).comp
      (continuous_id.prodMk continuous_const)
  -- the continuous representatives
  have h1 : chainT σ ε c 0 R α t (fun t' => G α t' s) =
      chainT σ ε c 0 R'' α t (fun t' => ∫ lam, φ lam * E lam t') := by
    rw [chainT_congr c 0 (F' := R3) α (fun j t' s' ht' hs' => ?_)
      (g' := fun t' => ∫ lam, φ lam * E lam t') (fun t' ht' => ?_) t ht]
    · refine chainT_congr_range c 0 α (fun j hj => ?_) t _
      have hj' : j ∈ Set.Ico 0 c.size := by simpa using hj
      simp only [hR3, hj', ↓reduceIte]
    · by_cases hj : j ∈ Set.Ico 0 c.size
      · simp only [hR3, hj, ↓reduceIte]
        exact hR j hj α t' s' ht' hs'
      · simp only [hR3, hj, ↓reduceIte]
    · rw [show (∫ lam, φ lam * E lam t') = ∫ lam, Cb (α ∘ fb) lam * e2 lam t' s from
        congrFun hG'' t']
      exact hG α t' s ht' hs
  rw [h1, chainT_fubini hε hĈ α (F := R'') (fun j t s => rfl) c 0 hinj0 hGc t ht]
  -- the pointwise expansion
  have h3 : ∀ z : ZT c, Mz Ĉ c 0 z *
      chainT σ ε c 0 (fun j _ => e2 (Λz c 0 z j)) α t (fun t' => ∫ lam, φ lam * E lam t') =
      ∫ lam, ∑ Y ∈ (adjSet c 0).powerset, ∑ Y' ∈ Y.powerset,
        (∏ j ∈ Y', PhiZ ζ (σ j) (α (σ j))) *
          (gTerm σ ε P fb Cb c (GJ Y) Y Y' α t s (z, lam) +
            gTerm σ ε P fb Cb c (GR Y) Y Y' α t s (z, lam)) := by
    intro z
    rw [chainT_exp_fubini hε (Λz c 0 z) c 0 hinj0 α hφ hEc hEB ht, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun lam => ?_)
    simp only [hE_def]
    rw [chainT_exp_expand hε hζ hc hinj hGJR α z lam.1 ht]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => ?_
    simp only [gTerm, hφ_def, hĈ_def]
    ring
  simp_rw [h3]
  -- the sections
  have hae : ∀ᵐ z : ZT c, ∀ Y ∈ (adjSet c 0).powerset, ∀ Y' ∈ Y.powerset,
      Integrable (fun lam => gTerm σ ε P fb Cb c (GJ Y) Y Y' α t s (z, lam)) ∧
        Integrable (fun lam => gTerm σ ε P fb Cb c (GR Y) Y Y' α t s (z, lam)) := by
    rw [eventually_all_finset]
    intro Y hY
    rw [eventually_all_finset]
    intro Y' hY'
    exact ((hint Y hY Y' hY').1.prod_right_ae).and ((hint Y hY Y' hY').2.prod_right_ae)
  rw [integral_congr_ae (hae.mono fun z hz => integral_sum2 _ _ _ _ _ hz)]
  rw [integral_sum2 _ _ _ _ _ fun Y hY Y' hY' =>
    ⟨(hint Y hY Y' hY').1.integral_prod_left, (hint Y hY Y' hY').2.integral_prod_left⟩]
  refine Finset.sum_congr rfl fun Y hY => Finset.sum_congr rfl fun Y' hY' => ?_
  have e1 : ∫ w, gTerm σ ε P fb Cb c (GJ Y) Y Y' α t s w =
      ∫ z, ∫ lam, gTerm σ ε P fb Cb c (GJ Y) Y Y' α t s (z, lam) :=
    integral_prod _ (hint Y hY Y' hY').1
  have e2 : ∫ w, gTerm σ ε P fb Cb c (GR Y) Y Y' α t s w =
      ∫ z, ∫ lam, gTerm σ ε P fb Cb c (GR Y) Y Y' α t s (z, lam) :=
    integral_prod _ (hint Y hY Y' hY').2
  rw [e1, e2]

end Bottom

end WaveTurbulence.ClassJR
