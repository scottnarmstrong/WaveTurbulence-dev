/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.L1
public import WaveTurbulence.Foundations.ClassJR.MCChainT

/-!
# Regularizing one variable through Volterra operators (DH21 §7.1)

The proofs of DH21 Lemmas 7.1 and 7.3 fix all variables but one, `x = α_j`, and compute
`[G]∫ K(x) dx = lim_{θ→0} ∫ K(x) e^{-πθ²x²} dx` (DH21 (gausspv)). Here `K(x)` is a Volterra chain in
which `x` enters a single factor. `RegTo Φ Ψ` records that the Gaussian regularization in `x` of a
family of time functions `z ↦ Φ x z` converges to `Ψ z` on `[0,1]`. It also records the bounds
that carry this through further Volterra operators.

* `RegTo.volterra_left`: a fixed Volterra operator on the left preserves `RegTo`.
* `RegTo.of_kernel`: a factor `volterra (M x) g` whose regularized kernel converges.
* `regTo_tr58`: the adjacent-pair core (DH21 Lemma 7.3). The regularized
  `𝒥_{α,μ} + ℛ_{α,μ} = I_{εα}I_{μ-εα} - Φ(εα)𝒥_{α[ ],μ}` tends to `+I_μ`. Since `𝒥_{α[ ],μ} = -I_μ`
  (F61), the integral over `α` of the `j ∉ Z` piece is minus the `j ∈ Z` piece.
* `regTo_sand`: the non-adjacent-pair core (DH21 Lemma 7.1). The regularized sandwich
  `I_{εα} T I_{μ-εα}` tends to `0`.
* `RegTo.integral_eq`: if the section is integrable, its integral is the limit.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

/-- **A Gaussian-regularized limit in one variable.** The family `x ↦ (z ↦ Φ x z)` is jointly
continuous and bounded on `ℝ × [0,1]`. Its regularizations `z ↦ greg θ (x ↦ Φ x z)` are bounded
uniformly for small `θ` and converge to `Ψ z` on `[0,1]` as `θ → 0+`. -/
structure RegTo (Φ : ℝ → ℝ → ℂ) (Ψ : ℝ → ℂ) : Prop where
  cont : Continuous (Function.uncurry Φ)
  bdd : ∃ C, ∀ x, ∀ z ∈ Icc (0 : ℝ) 1, ‖Φ x z‖ ≤ C
  regBdd : ∃ C, ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ z ∈ Icc (0 : ℝ) 1, ‖greg θ (fun x => Φ x z)‖ ≤ C
  lim : ∀ z ∈ Icc (0 : ℝ) 1, Tendsto (fun θ => greg θ (fun x => Φ x z)) (𝓝[>] 0) (𝓝 (Ψ z))

theorem stronglyMeasurable_greg_param {Φ : ℝ → ℝ → ℂ} (hΦ : Continuous (Function.uncurry Φ))
    (θ : ℝ) : StronglyMeasurable fun z => greg θ (fun x => Φ x z) := by
  unfold greg
  have h : StronglyMeasurable (fun p : ℝ × ℝ => (gw θ p.2 : ℂ) * Φ p.2 p.1) :=
    ((continuous_ofReal.comp ((continuous_gw θ).comp continuous_snd)).mul
      (hΦ.comp (continuous_snd.prodMk continuous_fst))).stronglyMeasurable
  exact h.integral_prod_right'

theorem eventually_pos_nhdsGT : ∀ᶠ θ in 𝓝[>] (0 : ℝ), 0 < θ := self_mem_nhdsWithin

theorem exists_bound_unit {g : ℝ → ℂ} (hg : Continuous g) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ Icc (0 : ℝ) 1, ‖g z‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc (0 : ℝ) 1))
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩

theorem norm_volterra_le {K : ℝ → ℝ → ℂ} {g : ℝ → ℂ} {CK Cg : ℝ} (hCK : 0 ≤ CK) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hK : ∀ s ∈ Icc (0 : ℝ) z, ‖K z s‖ ≤ CK)
    (hg : ∀ s ∈ Icc (0 : ℝ) z, ‖g s‖ ≤ Cg) : ‖volterra K g z‖ ≤ CK * Cg := by
  have hCg : 0 ≤ Cg := (norm_nonneg _).trans (hg 0 ⟨le_rfl, hz.1⟩)
  unfold volterra
  have hb : ∀ s ∈ uIoc (0 : ℝ) z, ‖K z s * g s‖ ≤ CK * Cg := fun s hs => by
    rw [uIoc_of_le hz.1] at hs
    rw [norm_mul]
    exact mul_le_mul (hK s ⟨hs.1.le, hs.2⟩) (hg s ⟨hs.1.le, hs.2⟩) (norm_nonneg _) hCK
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans ?_
  rw [sub_zero, abs_of_nonneg hz.1]
  calc CK * Cg * z ≤ CK * Cg * 1 := mul_le_mul_of_nonneg_left hz.2 (mul_nonneg hCK hCg)
    _ = CK * Cg := mul_one _

/-- **A fixed Volterra operator on the left.** -/
theorem RegTo.volterra_left {Φ : ℝ → ℝ → ℂ} {Ψ : ℝ → ℂ} (h : RegTo Φ Ψ) {A : ℝ → ℝ → ℂ}
    (hA : KCont A) : RegTo (fun x z => volterra A (Φ x) z) (volterra A Ψ) := by
  obtain ⟨CA, hCA0, hCA⟩ := hA.exists_bound
  obtain ⟨C, hC⟩ := h.bdd
  obtain ⟨C', hC'⟩ := h.regBdd
  have hFc : ∀ z, Continuous (Function.uncurry fun (x s : ℝ) => A z s * Φ x s) := fun z =>
    (hA.comp (continuous_const.prodMk continuous_snd)).mul h.cont
  -- `greg` commutes with the fixed operator
  have hcomm : ∀ θ, 0 < θ → ∀ z ∈ Icc (0 : ℝ) 1, greg θ (fun x => volterra A (Φ x) z) =
      volterra A (fun s => greg θ (fun x => Φ x s)) z := by
    intro θ hθ z hz
    unfold volterra
    rw [greg_intervalIntegral hθ (C := CA * C) (hFc z)]
    · exact intervalIntegral.integral_congr fun s _ => greg_const_mul θ _ _
    · intro x s hs
      rw [uIcc_of_le hz.1] at hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans hz.2⟩
      rw [norm_mul]
      exact mul_le_mul (hCA z s hz hs') (hC x s hs') (norm_nonneg _) hCA0
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Continuous fun p : ℝ × ℝ => ∫ s in (0 : ℝ)..p.2, A p.2 s * Φ p.1 s
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) s => A p.2 s * Φ p.1 s)
      ((hA.comp (continuous_fst.snd.prodMk continuous_snd)).mul
        (h.cont.comp (continuous_fst.fst.prodMk continuous_snd))) continuous_snd
  · refine ⟨CA * C, fun x z hz => norm_volterra_le hCA0 hz (fun s hs => hCA z s hz ⟨hs.1, hs.2.trans hz.2⟩)
      (fun s hs => hC x s ⟨hs.1, hs.2.trans hz.2⟩)⟩
  · refine ⟨CA * C', ?_⟩
    filter_upwards [hC', eventually_pos_nhdsGT] with θ hθ hθ0 z hz
    rw [hcomm θ hθ0 z hz]
    exact norm_volterra_le hCA0 hz (fun s hs => hCA z s hz ⟨hs.1, hs.2.trans hz.2⟩)
      (fun s hs => hθ s ⟨hs.1, hs.2.trans hz.2⟩)
  · intro z hz
    have e : (fun θ => greg θ (fun x => volterra A (Φ x) z)) =ᶠ[𝓝[>] 0]
        fun θ => volterra A (fun s => greg θ (fun x => Φ x s)) z := by
      filter_upwards [eventually_pos_nhdsGT] with θ hθ
      exact hcomm θ hθ z hz
    refine Tendsto.congr' e.symm ?_
    unfold volterra
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => CA * C') ?_ ?_
      intervalIntegrable_const ?_
    · exact Eventually.of_forall fun θ =>
        ((hA.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable.mul
          (stronglyMeasurable_greg_param h.cont θ)).aestronglyMeasurable
    · filter_upwards [hC'] with θ hθ
      refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le hz.1] at hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans hz.2⟩
      rw [norm_mul]
      exact mul_le_mul (hCA z s hz hs') (hθ s hs') (norm_nonneg _) hCA0
    · refine Eventually.of_forall fun s hs => ?_
      rw [uIoc_of_le hz.1] at hs
      exact (h.lim s ⟨hs.1.le, hs.2.trans hz.2⟩).const_mul _

/-- **A parametric factor whose regularized kernel converges.** If `M x` is a jointly continuous,
triangle-bounded family of kernels, and `gregK θ M` agrees on the triangle with continuous kernels
`R θ` that are bounded uniformly and converge to `L` below the diagonal, then `RegTo` holds for
`x ↦ volterra (M x) g` with limit `volterra L g`. -/
theorem RegTo.of_kernel {M : ℝ → ℝ → ℝ → ℂ} (hM : PCont M) {C : ℝ} (hMb : TriBdd M C)
    {R : ℝ → ℝ → ℝ → ℂ} (hRe : ∀ᶠ θ in 𝓝[>] (0 : ℝ), KEqOn (gregK θ M) (R θ))
    (hR : ∀ᶠ θ in 𝓝[>] (0 : ℝ), KCont (R θ)) {C' : ℝ}
    (hRb : ∀ᶠ θ in 𝓝[>] (0 : ℝ), KTriBdd (R θ) C') {L : ℝ → ℝ → ℂ}
    (hlim : ∀ t z, 0 ≤ z → z < t → t ≤ 1 → Tendsto (fun θ => R θ t z) (𝓝[>] 0) (𝓝 (L t z)))
    {g : ℝ → ℂ} (hg : Continuous g) :
    RegTo (fun x z => volterra (M x) g z) (volterra L g) := by
  obtain ⟨Cg, hCg0, hCg⟩ := exists_bound_unit hg
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hMb 0 0 0 le_rfl le_rfl zero_le_one)
  have hcomm : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ z ∈ Icc (0 : ℝ) 1,
      greg θ (fun x => volterra (M x) g z) = volterra (R θ) g z := by
    filter_upwards [hRe, eventually_pos_nhdsGT] with θ he hθ z hz
    rw [greg_volterra hθ hM hMb hg hz.1 hz.2, volterra_congr_tri he g hz]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Continuous fun p : ℝ × ℝ => ∫ s in (0 : ℝ)..p.2, M p.1 p.2 s * g s
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) s => M p.1 p.2 s * g s)
      ((hM.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))).mul
        (hg.comp continuous_snd)) continuous_snd
  · exact ⟨C * Cg, fun x z hz => norm_volterra_le hC0 hz
      (fun s hs => hMb x z s hs.1 hs.2 hz.2) (fun s hs => hCg s ⟨hs.1, hs.2.trans hz.2⟩)⟩
  · refine ⟨max C' 0 * Cg, ?_⟩
    filter_upwards [hcomm, hRb] with θ hθ hb z hz
    rw [hθ z hz]
    exact norm_volterra_le (le_max_right _ _) hz
      (fun s hs => (hb z s hs.1 hs.2 hz.2).trans (le_max_left _ _))
      (fun s hs => hCg s ⟨hs.1, hs.2.trans hz.2⟩)
  · intro z hz
    have e : (fun θ => greg θ (fun x => volterra (M x) g z)) =ᶠ[𝓝[>] 0]
        fun θ => volterra (R θ) g z := by
      filter_upwards [hcomm] with θ hθ
      exact hθ z hz
    exact (tendsto_volterra hR hRb hlim hg hz.1 hz.2).congr' e.symm

/-- **If the section is integrable, its integral is the regularized limit.** -/
theorem RegTo.integral_eq {Φ : ℝ → ℝ → ℂ} {Ψ : ℝ → ℂ} (h : RegTo Φ Ψ) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) (hi : Integrable fun x => Φ x z) : ∫ x, Φ x z = Ψ z :=
  tendsto_nhds_unique (tendsto_greg hi) (h.lim z hz)

/-! ### The two cores -/

/-- The regularized `𝒥 + ℛ` kernel `e^{πiμs} GI θ (t-s)`. -/
@[expose] noncomputable def rtrK (θ μ : ℝ) (t s : ℝ) : ℂ := iker μ t s * GI θ (t - s)

theorem kcont_rtrK (θ μ : ℝ) : KCont (rtrK θ μ) :=
  (kcont_iker μ).mul (continuous_ofReal.comp ((continuous_GI θ).comp (continuous_fst.sub continuous_snd)))

theorem kTriBdd_rtrK {θ : ℝ} (hθ : 0 < θ) (μ : ℝ) : KTriBdd (rtrK θ μ) 1 := by
  intro t s _ hst _
  unfold rtrK
  rw [norm_mul, norm_iker, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (GI_nonneg hθ (sub_nonneg.2 hst))]
  exact GI_le_one hθ (sub_nonneg.2 hst)

/-- **The adjacent-pair core** (DH21 Lemma 7.3). The `α`-regularization of
`volterra (𝒥_{α,μ} + ℛ_{α,μ}) g` tends to `volterra I_μ g`. -/
theorem regTo_tr58 {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (μ : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    RegTo (fun x z => volterra (tr58K ε μ x) g z) (volterra (iker μ) g) := by
  refine RegTo.of_kernel (pcont_tr58K ε μ) (triBdd_tr58K ε μ) (R := fun θ => rtrK θ μ) ?_
    (Eventually.of_forall fun θ => kcont_rtrK θ μ) (C' := 1) ?_ ?_ hg
  · filter_upwards [eventually_pos_nhdsGT] with θ hθ
    intro t s hs0 hst ht1
    exact gregK_tr58K hθ hε μ hs0 hst ht1
  · filter_upwards [eventually_pos_nhdsGT] with θ hθ
    exact kTriBdd_rtrK hθ μ
  · intro t z _ hzt _
    have := (continuous_ofReal.tendsto 1).comp (tendsto_GI (sub_pos.2 hzt))
    have h2 := this.const_mul (iker μ t z)
    simp only [Function.comp_def, ofReal_one, mul_one] at h2
    exact h2

/-- **The non-adjacent-pair core** (DH21 Lemma 7.1). The `α`-regularization of the sandwich
`volterra (I_{εα} T I_{μ-εα}) g` tends to `0`. -/
theorem regTo_sand {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (μ : ℝ) {T : ℝ → ℝ → ℂ} (hT : KCont T)
    {g : ℝ → ℂ} (hg : Continuous g) :
    RegTo (fun x z => volterra (sandK ε μ T x) g z) (fun _ => 0) := by
  obtain ⟨CT, hCT0, hCT⟩ := hT.exists_bound
  have hTb : KTriBdd T CT := fun t s hs0 hst ht1 =>
    hCT t s ⟨hs0.trans hst, ht1⟩ ⟨hs0, hst.trans ht1⟩
  have h := RegTo.of_kernel (pcont_sandK ε μ hT) (triBdd_sandK ε μ hCT0 hTb)
    (R := fun θ => rsandK θ μ T) ?_ (Eventually.of_forall fun θ => kcont_rsandK θ μ hT) (C' := CT) ?_
    (L := fun _ _ => 0) ?_ hg
  · have e : volterra (fun _ _ => (0 : ℂ)) g = fun _ => 0 := by
      funext z; simp [volterra]
    rwa [e] at h
  · filter_upwards [eventually_pos_nhdsGT] with θ hθ
    intro t s hs0 hst ht1
    exact gregK_sandK hθ hε μ hT hs0 hst ht1
  · filter_upwards [eventually_pos_nhdsGT] with θ hθ
    exact kTriBdd_rsandK hθ μ hCT0 hTb
  · intro t z _ hzt _
    exact tendsto_rsandK μ hT hzt.le

/-! ### Peeling one variable -/

section Peel

variable {V : Type*} [DecidableEq V]

/-- **The integral vanishes if every integrable section in `v` integrates to `0`.** -/
theorem mint_eq_zero_of_peel {W : Finset V} {v : V} (hv : v ∉ W) {F : (V → ℝ) → ℂ}
    {α₀ : V → ℝ} (hF : MInt (W ∪ {v}) F α₀)
    (h0 : ∀ α : V → ℝ, Integrable (fun x : ℝ => F (update α v x)) → ∫ x : ℝ, F (update α v x) = 0) :
    mint (W ∪ {v}) F α₀ = 0 := by
  rw [mint_union_singleton hv hF,
    mint_congr_ae (G := fun _ => 0) ((hF.union_singleton hv).mono fun y hy => h0 _ hy)]
  simp [mint]

/-- Removing one point `j` from an injective image. -/
theorem image_erase_union {σ : ℕ → V} {s : Finset ℕ} {j : ℕ} (hj : j ∈ s)
    (hinj : Set.InjOn σ ↑s) :
    s.image σ = (s.erase j).image σ ∪ {σ j} ∧ σ j ∉ (s.erase j).image σ := by
  refine ⟨?_, ?_⟩
  · rw [← Finset.image_singleton (f := σ), ← Finset.image_union, Finset.erase_union_eq j s hj]
  · rw [Finset.mem_image]
    rintro ⟨i, hi, hij⟩
    have hi' := Finset.mem_erase.1 hi
    exact hi'.1 (hinj (Finset.mem_coe.2 hi'.2) (Finset.mem_coe.2 hj) hij)

end Peel

end WaveTurbulence.Cancel
