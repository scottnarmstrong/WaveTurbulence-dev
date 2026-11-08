/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Expand
public import WaveTurbulence.Foundations.Flower.MkDefs.ChiDNorm

/-! # D7 SEL-RES / Pattern: the high/low dichotomy at the selected atoms (o73 Prop 20.1)

At each selected atom `v` and decoration: low (`𝓛_v`, `|ξ_v| < |β_v|/2`) or high (`𝓗_v`). Here `β_v = ζ δ L^{2γ} Ω_v`
and `ξ_v` is the frequency shift.
- `kernel_eq_sum_patterns`: the kernel is the sum over the `2^a` patterns (indicator times `patInd`, local to sel).
- `betaV_ge`: on the support `|β_v| ≥ μ M₂/2`, from the annular filter `chiDN(Ω_v/M₂)` (`chi0 ≡ 1` on `|u| < 1/2`).
  Only the zero set of the selected filter is used; `chiDN = chiD / chiDNorm` (R179) has the zero set of `chiD`.
- Each selected atom `v` has its own scale `M_v` (filter `chiDN(Ω_v/M_v)`; per-tree scales, finding F-C5b-1).
- `pattern_zero`: a pattern vanishes if one of its high atoms has `|ξ_v| < μM_v/4`.
- `pattern_bound`: on a pattern the low atoms have `|πα_v| ≥ λ_v = πμM_v/4`. Then `expand_bound_atom` gives
  `∏_{v∈Q} 12/λ_v` times any bound for the modifications `ModOK sel` of the original data. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ContDiff
namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKFine

variable {w d : ℕ} {G : Garden w}

/-! ### The annular filter -/

theorem deriv_chi0_eq_zero {x : ℝ} (hx : |x| < 1 / 2) : deriv WaveTurbulence.chi0 x = 0 := by
  have hev : WaveTurbulence.chi0 =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    have hopen : IsOpen {y : ℝ | |y| < 1 / 2} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds hx] with y hy
    unfold WaveTurbulence.chi0
    exact Real.smoothTransition.one_of_one_le (by have : |y| < 1 / 2 := hy; linarith)
  rw [hev.deriv_eq]; simp

/-- `chiD u ≠ 0` forces `|u| ≥ 1/2` (`chi0 ≡ 1` on `|u| < 1/2`). -/
theorem half_le_abs_of_chiD_ne {u : ℝ} (h : chiD u ≠ 0) : 1 / 2 ≤ |u| := by
  by_contra hlt
  push Not at hlt
  exact h (by unfold chiD; rw [deriv_chi0_eq_zero hlt, mul_zero])

/-- `chiDN u ≠ 0` forces `|u| ≥ 1/2`: the normalized filter `chiDN = chiD / chiDNorm` (R179) vanishes where `chiD`
does. -/
theorem half_le_abs_of_chiDN_ne {u : ℝ} (h : chiDN u ≠ 0) : 1 / 2 ≤ |u| :=
  half_le_abs_of_chiD_ne fun h0 => h (by unfold chiDN; rw [h0, zero_div])

/-- `chiDN` in product form: `chiDN u = (-u / chiDNorm) · χ₀'(u)`. -/
theorem chiDN_eq_mul : chiDN = fun u => -u / chiDNorm * deriv Fourier.chi0 u := by
  funext u
  unfold chiDN chiD
  rw [MkDefs.chi0_eq_fourier]
  ring

/-- `chiDN`, as a complex function, is smooth. -/
theorem contDiff_chiDNc : ContDiff ℝ ∞ fun u : ℝ => ((chiDN u : ℝ) : ℂ) := by
  have h1 : ContDiff ℝ ∞ (deriv Fourier.chi0) :=
    (contDiff_infty_iff_deriv.1 (Fourier.chi0_contDiff (n := ⊤))).2
  have h2 : ContDiff ℝ ∞ chiDN := by
    rw [chiDN_eq_mul]
    exact (contDiff_id.neg.div_const _).mul h1
  exact Complex.ofRealCLM.contDiff.comp h2

/-- `chiDN`, as a complex function, has compact support. -/
theorem hasCompactSupport_chiDNc : HasCompactSupport fun u : ℝ => ((chiDN u : ℝ) : ℂ) := by
  have h : HasCompactSupport chiDN := by
    rw [chiDN_eq_mul]
    exact Fourier.chi0_hasCompactSupport.deriv.mul_left
  exact h.comp_left Complex.ofReal_zero

-- [adapted] MkSlots/Findings.lean `exists_one_lt_abs_chiD` (sha256 in COPIED-SHA256SUMS): the mean value theorem on
-- `[1/2, 1]` gives `chiD u = 2u ≠ 0`.
/-- `chiDN` is not identically zero. -/
theorem exists_chiDN_ne_zero : ∃ u : ℝ, chiDN u ≠ 0 := by
  have hc : ContDiff ℝ 1 Fourier.chi0 := Fourier.chi0_contDiff
  have hcont : ContinuousOn Fourier.chi0 (Icc (1 / 2 : ℝ) 1) := hc.continuous.continuousOn
  have hdiff : DifferentiableOn ℝ Fourier.chi0 (Ioo (1 / 2 : ℝ) 1) :=
    (hc.differentiable one_ne_zero).differentiableOn
  obtain ⟨u, hu, hder⟩ := exists_deriv_eq_slope Fourier.chi0 (by norm_num : (1 / 2 : ℝ) < 1) hcont hdiff
  have h1 : Fourier.chi0 (1 / 2) = 1 := Fourier.chi0_eq_one (by norm_num [abs_of_pos])
  have h0 : Fourier.chi0 1 = 0 := Fourier.chi0_eq_zero (by norm_num)
  rw [h1, h0] at hder
  refine ⟨u, ?_⟩
  have hD : chiD u = 2 * u := by
    unfold chiD
    rw [MkDefs.chi0_eq_fourier, hder]
    norm_num
    ring
  unfold chiDN
  rw [hD]
  exact div_ne_zero (by linarith [hu.1]) chiDNorm_pos.ne'

/-- **The selected filter clause is not vacuous (R179).** `chiDN` is a complex Schwartz function, bounded by `1`, and
not identically zero. So the clause `π.filt v = some (M₂, ψ) ∧ ∀ u, ψ u = chiDN u` of `MarkedPieceBoundSelAt` and
`MarkedSumBoundSelAt` is compatible with `SoundMKFull.filt_ok`'s `‖ψ u‖ ≤ 1`. With `chiD` it was not:
`sup |chiD| > 1` (`MkSlots.exists_one_lt_abs_chiD`). -/
theorem exists_schwartz_chiDN :
    ∃ ψ : SchwartzMap ℝ ℂ, (∀ u, ψ u = (chiDN u : ℂ)) ∧ (∀ u, ‖ψ u‖ ≤ 1) ∧ ∃ u, ψ u ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_chiDN_ne_zero
  exact ⟨hasCompactSupport_chiDNc.toSchwartzMap contDiff_chiDNc, fun _ => rfl, fun u => norm_chiDN_le_one u,
    u, Complex.ofReal_ne_zero.2 hu⟩

/-! ### The dichotomy at a selected atom -/

/-- The resonance part `β_v = ζ δ L^{2γ} Ω_v` of the selected frequency. -/
def betaV (L γ δ : ℝ) (v : GBranch G.tree) (k : GNode G.tree → Mom d) : ℝ :=
  (((G.sign v.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) * omegaNode G k v

/-- `L_v`: the shift `ξ_v` is less than half the resonance part (o73 `𝓛_v`). -/
def lowInd (L γ δ ξ : ℝ) (v : GBranch G.tree) (k : GNode G.tree → Mom d) : ℝ :=
  if |ξ| < |betaV L γ δ v k| / 2 then 1 else 0

/-- The pattern indicator: the atoms of `Q` low, those of `sel \ Q` high. -/
def patInd (L γ δ : ℝ) (ξ : GBranch G.tree → ℝ) (sel Q : Finset (GBranch G.tree)) (k : GNode G.tree → Mom d) : ℝ :=
  (∏ v ∈ Q, lowInd L γ δ (ξ v) v k) * ∏ v ∈ sel \ Q, (1 - lowInd L γ δ (ξ v) v k)

theorem lowInd_mem (L γ δ ξ : ℝ) (v : GBranch G.tree) (k : GNode G.tree → Mom d) :
    lowInd L γ δ ξ v k = 0 ∨ lowInd L γ δ ξ v k = 1 := by unfold lowInd; split_ifs <;> simp

theorem patInd_mem (L γ δ : ℝ) (ξ : GBranch G.tree → ℝ) (sel Q : Finset (GBranch G.tree))
    (k : GNode G.tree → Mom d) : 0 ≤ patInd L γ δ ξ sel Q k ∧ patInd L γ δ ξ sel Q k ≤ 1 := by
  have h01 : ∀ v, 0 ≤ lowInd L γ δ (ξ v) v k ∧ lowInd L γ δ (ξ v) v k ≤ 1 := fun v => by
    rcases lowInd_mem L γ δ (ξ v) v k with h | h <;> rw [h] <;> norm_num
  unfold patInd
  refine ⟨mul_nonneg (prod_nonneg fun v _ => (h01 v).1) (prod_nonneg fun v _ => by linarith [(h01 v).2]),
    ?_⟩
  calc _ ≤ 1 * 1 := mul_le_mul (prod_le_one₀ (fun v _ => (h01 v).1) fun v _ => (h01 v).2)
        (prod_le_one₀ (fun v _ => by linarith [(h01 v).2]) fun v _ => by linarith [(h01 v).1])
        (prod_nonneg fun v _ => by linarith [(h01 v).2]) zero_le_one
    _ = 1 := one_mul 1

theorem sum_patInd (L γ δ : ℝ) (ξ : GBranch G.tree → ℝ) (sel : Finset (GBranch G.tree))
    (k : GNode G.tree → Mom d) : ∑ Q ∈ sel.powerset, patInd L γ δ ξ sel Q k = 1 := by
  unfold patInd
  rw [← Finset.prod_add]
  simp

theorem betaV_local (L γ δ : ℝ) (v : GBranch G.tree) (k k' : GNode G.tree → Mom d)
    (h : ∀ i : Fin 3, k (v.child i) = k' (v.child i) ∧ k v.toNode = k' v.toNode) :
    betaV L γ δ v k = betaV L γ δ v k' := by
  unfold betaV omegaNode
  rw [(h 0).1, (h 1).1, (h 2).1, (h 0).2]

theorem patInd_local (L γ δ : ℝ) (ξ : GBranch G.tree → ℝ) (sel Q : Finset (GBranch G.tree)) (hQ : Q ⊆ sel)
    (k k' : GNode G.tree → Mom d)
    (h : ∀ a ∈ sel, ∀ i : Fin 3, k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) :
    patInd L γ δ ξ sel Q k = patInd L γ δ ξ sel Q k' := by
  unfold patInd lowInd
  congr 1
  · exact Finset.prod_congr rfl fun v hv => by rw [betaV_local L γ δ v k k' (h v (hQ hv))]
  · exact Finset.prod_congr rfl fun v hv => by rw [betaV_local L γ δ v k k' (h v (Finset.mem_sdiff.1 hv).1)]

/-- **Pattern decomposition**: the kernel is the sum of the pattern kernels. -/
theorem kernel_eq_sum_patterns (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (ξ : GBranch G.tree → ℝ) (sel : Finset (GBranch G.tree)) :
    splicedKernelMK G D L γ η δ base roots =
      ∑ Q ∈ sel.powerset, splicedKernelMK G (modData D D.fix (patInd L γ δ ξ sel Q)) L γ η δ base roots := by
  conv_lhs => rw [← modData_self D]
  simp only [kernel_eq_sum hP D hD hL γ η δ base roots]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  rw [← Complex.ofReal_sum, sum_patInd]

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKFine

variable {w d : ℕ} {G : Garden w}

theorem abs_sign_cast (u : ℤˣ) : |(((u : ℤˣ) : ℤ) : ℝ)| = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

theorem abs_betaV (L γ δ : ℝ) (hδ : 0 ≤ δ) (hL : 0 ≤ L) (v : GBranch G.tree) (k : GNode G.tree → Mom d) :
    |betaV L γ δ v k| = δ * L ^ (2 * γ) * |omegaNode G k v| := by
  unfold betaV
  rw [abs_mul, abs_mul, abs_mul, abs_sign_cast, abs_of_nonneg hδ, abs_of_nonneg (Real.rpow_nonneg hL _), one_mul]

/-- On the support, the filter of a selected atom is nonzero. -/
theorem filter_ne_of_ampMK (D : SplicedKernelDataMK G d) {L γ η : ℝ} {base : Mom d}
    {z : GNode G.tree → (Fin d → ℤ)} (h : ampMK G D L γ η base z ≠ 0) {v : GBranch G.tree} {M : ℝ}
    {ψ : SchwartzMap ℝ ℂ} (hv : D.filt v = some (M, ψ)) :
    ψ (omegaNode G (cosetDecoration G L base z) v / M) ≠ 0 := by
  have h1 : D.atomW (cosetDecoration G L base z) ≠ 0 := left_ne_zero_of_mul h
  have h2 := left_ne_zero_of_mul h1
  have h3 := (Finset.prod_ne_zero_iff.1 h2) v (mem_univ v)
  rwa [hv] at h3

/-- On the support, a selected atom has `|β_v| ≥ μ M₂ / 2` (the annular filter `chiDN(Ω_v/M₂)`). -/
theorem betaV_ge (D : SplicedKernelDataMK G d) {L γ η δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) {base : Mom d}
    {z : GNode G.tree → (Fin d → ℤ)} (h : ampMK G D L γ η base z ≠ 0) {v : GBranch G.tree} {M : ℝ} (hM : 0 < M)
    {ψ : SchwartzMap ℝ ℂ} (hv : D.filt v = some (M, ψ)) (hψ : ∀ u, ψ u = (chiDN u : ℂ)) :
    δ * L ^ (2 * γ) * M / 2 ≤ |betaV L γ δ v (cosetDecoration G L base z)| := by
  have h1 := filter_ne_of_ampMK D h hv
  rw [hψ] at h1
  have h2 : chiDN (omegaNode G (cosetDecoration G L base z) v / M) ≠ 0 := fun h0 => h1 (by rw [h0]; simp)
  have h3 := half_le_abs_of_chiDN_ne h2
  rw [abs_div, abs_of_pos hM, le_div_iff₀ hM] at h3
  rw [abs_betaV L γ δ hδ hL]
  have hμ : 0 ≤ δ * L ^ (2 * γ) := mul_nonneg hδ (Real.rpow_nonneg hL _)
  nlinarith

/-- A pattern with a high atom `v` whose shift is below `μM_v/4` vanishes (per-atom scales `M v`). -/
theorem pattern_zero (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (hδ : 0 ≤ δ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (sel Q : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ)
    (hsel : ∀ v ∈ sel, ∃ ψ : SchwartzMap ℝ ℂ, D.filt v = some (M v, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ))
    {v : GBranch G.tree} (hv : v ∈ sel \ Q) (hM : 0 < M v) (hsmall : |D.frequency v| < δ * L ^ (2 * γ) * M v / 4) :
    splicedKernelMK G (modData D D.fix (patInd L γ δ D.frequency sel Q)) L γ η δ base roots = 0 := by
  rw [kernel_eq_sum hP D hD hL γ η δ base roots]
  refine (mul_eq_zero_of_right _ (Finset.sum_eq_zero fun z _ => ?_))
  by_cases h0 : ampMK G D L γ η base z.1 = 0
  · simp [h0]
  obtain ⟨ψ, hψ, hψc⟩ := hsel v (Finset.mem_sdiff.1 hv).1
  have hβ := betaV_ge D hL.le hδ h0 hM hψ hψc
  have hlow : lowInd L γ δ (D.frequency v) v (cosetDecoration G L base z.1) = 1 := by
    unfold lowInd; rw [ite_eq_left]; linarith
  have hpat : patInd L γ δ D.frequency sel Q (cosetDecoration G L base z.1) = 0 := by
    unfold patInd
    rw [Finset.prod_eq_zero hv (by rw [hlow]; ring), mul_zero]
  rw [hpat]; simp

/-- On a pattern, a low atom has selected frequency at least `π μ M₂ / 4`. -/
theorem selFreq_ge_of_low (D : SplicedKernelDataMK G d) {L γ η δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) {base : Mom d}
    (sel Q : Finset (GBranch G.tree)) {v : GBranch G.tree} (hvQ : v ∈ Q) {M : ℝ} (hM : 0 < M)
    {ψ : SchwartzMap ℝ ℂ} (hv : D.filt v = some (M, ψ)) (hψ : ∀ u, ψ u = (chiDN u : ℂ))
    {z : GNode G.tree → (Fin d → ℤ)}
    (hz : ampMK G (modData D D.fix (patInd L γ δ D.frequency sel Q)) L γ η base z ≠ 0) :
    Real.pi * (δ * L ^ (2 * γ) * M) / 4 ≤ |selFreq D L γ δ v (cosetDecoration G L base z)| := by
  rw [ampMK_modData] at hz
  have h0 : ampMK G D L γ η base z ≠ 0 := left_ne_zero_of_mul hz
  have hp : patInd L γ δ D.frequency sel Q (cosetDecoration G L base z) ≠ 0 := by
    intro h; apply hz; rw [h]; simp
  have hlow : lowInd L γ δ (D.frequency v) v (cosetDecoration G L base z) = 1 := by
    rcases lowInd_mem L γ δ (D.frequency v) v (cosetDecoration G L base z) with h | h
    · exact absurd (by unfold patInd; rw [Finset.prod_eq_zero hvQ h, zero_mul]) hp
    · exact h
  have hlt : |D.frequency v| < |betaV L γ δ v (cosetDecoration G L base z)| / 2 := by
    unfold lowInd at hlow; split_ifs at hlow with hh
    · exact hh
    · simp at hlow
  have hβ := betaV_ge D hL hδ h0 hM hv hψ
  have he : selFreq D L γ δ v (cosetDecoration G L base z) =
      Real.pi * (betaV L γ δ v (cosetDecoration G L base z) + D.frequency v) := rfl
  rw [he, abs_mul, abs_of_pos Real.pi_pos]
  have htri : |betaV L γ δ v (cosetDecoration G L base z)| - |D.frequency v| ≤
      |betaV L γ δ v (cosetDecoration G L base z) + D.frequency v| := by
    have := abs_add_le (betaV L γ δ v (cosetDecoration G L base z) + D.frequency v) (-D.frequency v)
    rw [add_neg_cancel_right, abs_neg] at this; linarith
  have : δ * L ^ (2 * γ) * M / 4 ≤ |betaV L γ δ v (cosetDecoration G L base z) + D.frequency v| := by linarith
  nlinarith [Real.pi_pos]

/-- Expanding the low atoms of a pattern produces modifications of the original data. -/
theorem ModOK.of_pattern {sel Q : Finset (GBranch G.tree)} (hQ : Q ⊆ sel) {D D' : SplicedKernelDataMK G d}
    {L γ δ : ℝ} (h : ModOK Q (modData D D.fix (patInd L γ δ D.frequency sel Q)) D') : ModOK sel D D' := by
  obtain ⟨hd, hf, ⟨g, hg, hgl, hi⟩, ⟨Rc, hRc, hc, hb⟩⟩ := h
  refine ⟨hd, hf, ⟨fun k => patInd L γ δ D.frequency sel Q k * g k, fun k => ?_, fun k k' hk => ?_,
    fun k => ?_⟩, ⟨Rc, hRc.trans (card_le_card hQ), fun b hb' => ?_, fun b hb' => hb b hb'⟩⟩
  · have h1 := patInd_mem L γ δ D.frequency sel Q k
    exact ⟨mul_nonneg h1.1 (hg k).1, (mul_le_mul h1.2 (hg k).2 (hg k).1 zero_le_one).trans_eq (one_mul 1)⟩
  · show patInd L γ δ D.frequency sel Q k * g k = patInd L γ δ D.frequency sel Q k' * g k'
    rw [patInd_local L γ δ D.frequency sel Q hQ k k' hk, hgl k k' fun a ha => hk a (hQ ha)]
  · rw [hi]; show D.ind k * patInd L γ δ D.frequency sel Q k * g k = _; ring
  · have := hc b hb'
    simp only [Finset.mem_union] at this ⊢
    rcases this with h | h
    · exact Or.inl (hQ h)
    · exact Or.inr h

/-- **The pattern bound** (per-atom scales `M v`): a pattern is at most `∏_{v∈Q} 12/λ_v` times any bound for the
modifications of the original data, `λ_v = π μ M_v / 4`. -/
theorem pattern_bound (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (hδ : 0 < δ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (sel Q : Finset (GBranch G.tree)) (hQ : Q ⊆ sel)
    (hone : ∀ a ∈ sel, ∀ b ∈ sel, a.1.1 = b.1.1 → a = b) (M : GBranch G.tree → ℝ) (hM : ∀ v ∈ sel, 0 < M v)
    (hsel : ∀ v ∈ sel, D.fix v = none ∧ ∃ ψ : SchwartzMap ℝ ℂ, D.filt v = some (M v, ψ) ∧ ∀ u, ψ u = (chiDN u : ℂ))
    (Bnd : ℝ) (hB0 : 0 ≤ Bnd) (hB : ∀ D', ModOK sel D D' → ‖splicedKernelMK G D' L γ η δ base roots‖ ≤ Bnd) :
    ‖splicedKernelMK G (modData D D.fix (patInd L γ δ D.frequency sel Q)) L γ η δ base roots‖ ≤
      (∏ v ∈ Q, 12 / (Real.pi * (δ * L ^ (2 * γ) * M v) / 4)) * Bnd := by
  have hlam : ∀ v ∈ Q, 0 < Real.pi * (δ * L ^ (2 * γ) * M v) / 4 := fun v hv => by
    have := Real.rpow_pos_of_pos hL (2 * γ); have := hM v (hQ hv); positivity
  refine expand_bound_atom hP hL γ η δ base roots (fun v => Real.pi * (δ * L ^ (2 * γ) * M v) / 4) Bnd hB0 Q _ hlam
    hD (fun a ha b hb => hone a (hQ ha) b (hQ hb)) (fun v hv => (hsel v (hQ hv)).1)
    (fun v hv z hz => ?_) (fun D' hD' => hB D' (ModOK.of_pattern hQ hD'))
  obtain ⟨ψ, hψ, hψc⟩ := (hsel v (hQ hv)).2
  rw [selFreq_congr (D := D) (D' := modData D D.fix (patInd L γ δ D.frequency sel Q)) rfl]
  exact selFreq_ge_of_low D hL.le hδ.le sel Q hv (hM v (hQ hv)) hψ hψc hz

end WaveTurbulence.Flower.SelRes
