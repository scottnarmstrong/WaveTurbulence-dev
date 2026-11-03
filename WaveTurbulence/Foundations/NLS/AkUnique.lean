/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkGronwall

/-!
# Uniqueness for the `a`-system in the class `Z^{d+1}`

* `enorm_aNonlin_sub_le`: the trilinear difference estimate
  `|𝒞(f,f̄,f)ₙ - 𝒞(g,ḡ,g)ₙ| ≤ κ (T(f-g,f,f) + T(g,f-g,f) + T(g,g,f-g))ₙ`, `T = tripleAbs`;
* `IsAkSolution.exists_aNonlin_majorant`: a summable majorant of the right side of (akeqn);
* `IsAkSolution.eq_of_eq`: two solutions of (akeqn)–(akeqn2) on `[0, 𝔇]` in the class
  `IsAkBounded` with the same data coincide (`ℓ¹` Gronwall; the uniqueness used at TARGET
  L795–L797 and in the Wave B proposal B1.1).
-/

public section

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped ENNReal

namespace WaveTurbulence

variable {d : ℕ}

/-! ### `ℓ¹` bookkeeping -/

theorem wt_zero (n : Fin d → ℤ) : wt 0 n = 1 := by simp [wt]

theorem wnorm_zero_eq (f : (Fin d → ℤ) → ℂ) : wnorm 0 f = ∑' n, ‖f n‖ₑ := by
  simp [wnorm, wt_zero]

theorem wnorm_zero_eq_ofReal {f : (Fin d → ℤ) → ℂ} (hf : Summable fun n => ‖f n‖) :
    wnorm 0 f = ENNReal.ofReal (∑' n, ‖f n‖) := by
  rw [wnorm_zero_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hf]
  simp [ofReal_norm]

theorem tsum_tripleAbs_le (f g h : (Fin d → ℤ) → ℂ) :
    ∑' n, tripleAbs f g h n ≤ wnorm 0 f * wnorm 0 g * wnorm 0 h := by
  simpa [wt_zero] using tsum_wt_mul_tripleAbs_le 0 f g h

theorem tripleAbs_mono {f g h f' g' h' : (Fin d → ℤ) → ℂ} (hf : ∀ m, ‖f m‖ ≤ ‖f' m‖)
    (hg : ∀ m, ‖g m‖ ≤ ‖g' m‖) (hh : ∀ m, ‖h m‖ ≤ ‖h' m‖) (n : Fin d → ℤ) :
    tripleAbs f g h n ≤ tripleAbs f' g' h' n :=
  ENNReal.tsum_le_tsum fun q => by
    gcongr
    · exact enorm_le_iff_norm_le.2 (hf _)
    · exact enorm_le_iff_norm_le.2 (hg _)
    · exact enorm_le_iff_norm_le.2 (hh _)

/-- The majorant family `m ↦ C (1 + ‖m‖)^{-(d+1)}`. -/
def majorant (C : ℝ) (m : Fin d → ℤ) : ℂ := ((C * ((1 + ‖m‖) ^ (d + 1))⁻¹ : ℝ) : ℂ)

theorem norm_majorant {C : ℝ} (hC : 0 ≤ C) (m : Fin d → ℤ) :
    ‖majorant C m‖ = C * ((1 + ‖m‖) ^ (d + 1))⁻¹ := by
  rw [majorant, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem summable_norm_majorant {C : ℝ} (hC : 0 ≤ C) :
    Summable fun m : Fin d → ℤ => ‖majorant C m‖ := by
  simp_rw [norm_majorant hC]
  exact summable_inv_one_add_norm_pow.mul_left C

theorem wnorm_zero_majorant_ne_top {C : ℝ} (hC : 0 ≤ C) :
    wnorm 0 (majorant (d := d) C) ≠ ∞ := by
  rw [wnorm_zero_eq_ofReal (summable_norm_majorant hC)]
  exact ENNReal.ofReal_ne_top

/-! ### The trilinear difference estimate -/

theorem summable_aNonlin_terms {f : (Fin d → ℤ) → ℂ} (hf : Summable fun m => ‖f m‖)
    (L γ δ s : ℝ) (n : Fin d → ℤ) :
    Summable fun q : (Fin d → ℤ) × (Fin d → ℤ) =>
      (epsCoef q.1 q.2 (n - q.1 + q.2) : ℂ) *
        exp (((((1 : ℤ) : ℝ) * Real.pi * δ * L ^ (2 * γ) * resonance L q.1 q.2 (n - q.1 + q.2) n *
          s : ℝ) : ℂ) * I) * f q.1 * (starRingEnd ℂ) (f q.2) * f (n - q.1 + q.2) := by
  refine Summable.of_norm_bounded (summable_norm_cubic_terms hf n) fun q => ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one, Complex.norm_conj]
  calc |epsCoef q.1 q.2 (n - q.1 + q.2)| * ‖f q.1‖ * ‖f q.2‖ * ‖f (n - q.1 + q.2)‖
      ≤ 1 * ‖f q.1‖ * ‖f q.2‖ * ‖f (n - q.1 + q.2)‖ := by gcongr; exact abs_epsCoef_le _ _ _
    _ = _ := by ring

/-- The trilinear difference estimate for the nonlinearity of (akeqn2). -/
theorem enorm_aNonlin_sub_le (L γ δ s : ℝ) {f g : (Fin d → ℤ) → ℂ}
    (hf : Summable fun m => ‖f m‖) (hg : Summable fun m => ‖g m‖) (n : Fin d → ℤ) :
    ‖aNonlin L γ δ 1 s f (fun m => (starRingEnd ℂ) (f m)) f n -
        aNonlin L γ δ 1 s g (fun m => (starRingEnd ℂ) (g m)) g n‖ₑ ≤
      ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))| *
        (tripleAbs (f - g) f f n + tripleAbs g (f - g) f n + tripleAbs g g (f - g) n) := by
  rw [aNonlin_eq_tsum_pairs, aNonlin_eq_tsum_pairs, ← mul_sub,
    ← (summable_aNonlin_terms hf L γ δ s n).tsum_sub (summable_aNonlin_terms hg L γ δ s n),
    enorm_mul, enorm_mul]
  have hI : ‖I * ((1 : ℤ) : ℂ)‖ₑ = 1 := by simp [← ofReal_norm]
  rw [hI, mul_one]
  gcongr
  · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  · refine enorm_tsum_le_tsum_enorm.trans ?_
    simp only [tripleAbs, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun q => ?_
    set e := (epsCoef q.1 q.2 (n - q.1 + q.2) : ℂ) *
      exp (((((1 : ℤ) : ℝ) * Real.pi * δ * L ^ (2 * γ) * resonance L q.1 q.2 (n - q.1 + q.2) n *
        s : ℝ) : ℂ) * I) with he
    have hen : ‖e‖ ≤ 1 := by
      rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
        mul_one]
      exact abs_epsCoef_le _ _ _
    set a₁ := f q.1
    set a₂ := f q.2
    set a₃ := f (n - q.1 + q.2)
    set b₁ := g q.1
    set b₂ := g q.2
    set b₃ := g (n - q.1 + q.2)
    have hid : e * a₁ * (starRingEnd ℂ) a₂ * a₃ - e * b₁ * (starRingEnd ℂ) b₂ * b₃ =
        e * ((a₁ - b₁) * (starRingEnd ℂ) a₂ * a₃ + b₁ * (starRingEnd ℂ) (a₂ - b₂) * a₃ +
          b₁ * (starRingEnd ℂ) b₂ * (a₃ - b₃)) := by
      rw [map_sub]; ring
    rw [hid, enorm_mul]
    calc ‖e‖ₑ * ‖(a₁ - b₁) * (starRingEnd ℂ) a₂ * a₃ + b₁ * (starRingEnd ℂ) (a₂ - b₂) * a₃ +
          b₁ * (starRingEnd ℂ) b₂ * (a₃ - b₃)‖ₑ
        ≤ 1 * (‖(a₁ - b₁) * (starRingEnd ℂ) a₂ * a₃‖ₑ + ‖b₁ * (starRingEnd ℂ) (a₂ - b₂) * a₃‖ₑ +
            ‖b₁ * (starRingEnd ℂ) b₂ * (a₃ - b₃)‖ₑ) := by
          gcongr
          · rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.2 hen
          · exact (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
      _ = _ := by
          have hc : ∀ z : ℂ, ‖(starRingEnd ℂ) z‖ₑ = ‖z‖ₑ := fun z => by
            rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
          simp only [one_mul, enorm_mul, hc, Pi.sub_apply]
          rfl

/-! ### Majorants along a solution -/

section Solutions

variable {L γ δ 𝔇 : ℝ} {c : (Fin d → ℤ) → ℂ} {a b : ℝ → (Fin d → ℤ) → ℂ}

/-- A summable majorant of the right side of (akeqn) along a classed solution. -/
theorem IsAkSolution.exists_aNonlin_majorant (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a) :
    ∃ Q : (Fin d → ℤ) → ℝ, Summable Q ∧ ∀ n, ∀ t ∈ Icc 0 𝔇,
      ‖aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n‖ ≤ Q n := by
  obtain ⟨C, hC0, hC⟩ := ha.2.1.exists_norm_le hL
  set κ := ENNReal.ofReal |δ / (2 * L ^ ((d : ℝ) - γ))|
  set B := majorant (d := d) C
  have hW := wnorm_zero_majorant_ne_top (d := d) hC0
  have hfin : ∑' n, κ * tripleAbs B B B n ≠ ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hW hW) hW)
        (tsum_tripleAbs_le B B B))
  refine ⟨fun n => (κ * tripleAbs B B B n).toReal, ENNReal.summable_toReal hfin,
    fun n t ht => ?_⟩
  have hn : κ * tripleAbs B B B n ≠ ∞ := ne_top_of_le_ne_top hfin (ENNReal.le_tsum (f := fun n => κ * tripleAbs B B B n) n)
  rw [← toReal_enorm]
  refine ENNReal.toReal_mono hn ((enorm_aNonlin_le L γ δ t _ _ _ n).trans ?_)
  gcongr
  refine tripleAbs_mono (fun m => ?_) (fun m => ?_) (fun m => ?_) n <;>
    simp only [norm_majorant hC0, B, Complex.norm_conj] <;> exact hC t ht m

theorem IsAkSolution.summable_norm (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a) {t : ℝ}
    (ht : t ∈ Icc 0 𝔇) : Summable fun m => ‖a t m‖ := by
  obtain ⟨C, hC0, hC⟩ := ha.2.1.exists_norm_le hL
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => hC t ht m)
    (summable_inv_one_add_norm_pow.mul_left C)

/-- **Uniqueness** for (akeqn)–(akeqn2) in the class `Z^{d+1}`: two solutions on `[0, 𝔇]` with
the same data coincide. -/
theorem IsAkSolution.eq_of_eq (hL : 0 < L) (ha : IsAkSolution L γ δ 𝔇 c a)
    (hb : IsAkSolution L γ δ 𝔇 c b) : ∀ t ∈ Icc 0 𝔇, a t = b t := by
  obtain ⟨Ca, hCa0, hCa⟩ := ha.2.1.exists_norm_le hL
  obtain ⟨Cb, hCb0, hCb⟩ := hb.2.1.exists_norm_le hL
  obtain ⟨Qa, hQa, hQa'⟩ := ha.exists_aNonlin_majorant hL
  obtain ⟨Qb, hQb, hQb'⟩ := hb.exists_aNonlin_majorant hL
  set S := ∑' m : Fin d → ℤ, ((1 + ‖m‖) ^ (d + 1))⁻¹ with hS
  set κ := |δ / (2 * L ^ ((d : ℝ) - γ))|
  set K := κ * ((Ca * S) * (Ca * S) + (Cb * S) * (Ca * S) + (Cb * S) * (Cb * S)) with hK
  have hS0 : 0 ≤ S := tsum_nonneg fun m => by positivity
  have hWa : ∀ t ∈ Icc 0 𝔇, ∑' m, ‖a t m‖ ≤ Ca * S := fun t ht => by
    rw [hS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun m => hCa t ht m) (ha.summable_norm hL ht)
      (summable_inv_one_add_norm_pow.mul_left Ca)
  have hWb : ∀ t ∈ Icc 0 𝔇, ∑' m, ‖b t m‖ ≤ Cb * S := fun t ht => by
    rw [hS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun m => hCb t ht m) (hb.summable_norm hL ht)
      (summable_inv_one_add_norm_pow.mul_left Cb)
  set F : (Fin d → ℤ) → ℝ → ℂ := fun n s =>
    aNonlin L γ δ 1 s (a s) (fun m => (starRingEnd ℂ) (a s m)) (a s) n -
      aNonlin L γ δ 1 s (b s) (fun m => (starRingEnd ℂ) (b s m)) (b s) n with hF
  have key := tsum_weighted_le_exp (ψ := fun n t => a t n - b t n) (G := F) (w := fun _ => 1)
    (T := 𝔇) (K := K) (by positivity) (fun _ => zero_le_one)
    (fun n => (ha.continuousOn n).sub (hb.continuousOn n))
    (fun n => (ha.continuousOn_aNonlin hL n).sub (hb.continuousOn_aNonlin hL n))
    (fun n t ht => ?heq)
    (P := fun n => (Ca + Cb) * ((1 + ‖n‖) ^ (d + 1))⁻¹) (Q := fun n => Qa n + Qb n)
    (summable_inv_one_add_norm_pow.mul_left _) (hQa.add hQb)
    (fun n t ht => ?hP) (fun n t ht => ?hQ) (fun t ht => ?hbound)
  case heq =>
    rw [ha.eq_add_integral hL ht n, hb.eq_add_integral hL ht n, congrFun ha.1 n,
      congrFun hb.1 n, sub_self, zero_add]
    simp only [hF]
    rw [intervalIntegral.integral_sub]
    · ring
    · exact ((ha.continuousOn_aNonlin hL n).mono
        (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    · exact ((hb.continuousOn_aNonlin hL n).mono
        (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  case hP =>
    rw [one_mul, add_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hCa t ht n) (hCb t ht n))
  case hQ =>
    rw [one_mul]
    exact (norm_sub_le _ _).trans (add_le_add (hQa' n t ht) (hQb' n t ht))
  case hbound =>
    simp only [one_mul]
    have hsa := ha.summable_norm hL ht
    have hsb := hb.summable_norm hL ht
    have hsd : Summable fun m => ‖(a t - b t) m‖ :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => norm_sub_le _ _) (hsa.add hsb)
    have hE : ∑' n, ‖F n t‖ₑ ≤ ENNReal.ofReal κ *
        (wnorm 0 (a t - b t) * wnorm 0 (a t) * wnorm 0 (a t) +
          wnorm 0 (b t) * wnorm 0 (a t - b t) * wnorm 0 (a t) +
          wnorm 0 (b t) * wnorm 0 (b t) * wnorm 0 (a t - b t)) := by
      calc ∑' n, ‖F n t‖ₑ ≤ ∑' n, ENNReal.ofReal κ * (tripleAbs (a t - b t) (a t) (a t) n +
            tripleAbs (b t) (a t - b t) (a t) n + tripleAbs (b t) (b t) (a t - b t) n) :=
            ENNReal.tsum_le_tsum fun n => enorm_aNonlin_sub_le L γ δ t hsa hsb n
        _ ≤ _ := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add]
            gcongr
            · exact tsum_tripleAbs_le _ _ _
            · exact tsum_tripleAbs_le _ _ _
            · exact tsum_tripleAbs_le _ _ _
    rw [wnorm_zero_eq_ofReal hsd, wnorm_zero_eq_ofReal hsa, wnorm_zero_eq_ofReal hsb] at hE
    set D := ∑' m, ‖(a t - b t) m‖
    set A := ∑' m, ‖a t m‖
    set Bt := ∑' m, ‖b t m‖
    have hD0 : 0 ≤ D := tsum_nonneg fun _ => norm_nonneg _
    have hA0 : 0 ≤ A := tsum_nonneg fun _ => norm_nonneg _
    have hB0 : 0 ≤ Bt := tsum_nonneg fun _ => norm_nonneg _
    have hreal : ∑' n, ‖F n t‖ ≤ κ * (D * A * A + Bt * D * A + Bt * Bt * D) := by
      have hp : ∀ x y z : ℝ, ENNReal.ofReal x * ENNReal.ofReal y * ENNReal.ofReal z ≠ ∞ :=
        fun x y z => ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
      have hs2 : ENNReal.ofReal D * ENNReal.ofReal A * ENNReal.ofReal A +
          ENNReal.ofReal Bt * ENNReal.ofReal D * ENNReal.ofReal A ≠ ∞ :=
        ENNReal.add_ne_top.2 ⟨hp _ _ _, hp _ _ _⟩
      have hfin : ENNReal.ofReal κ * (ENNReal.ofReal D * ENNReal.ofReal A * ENNReal.ofReal A +
          ENNReal.ofReal Bt * ENNReal.ofReal D * ENNReal.ofReal A +
          ENNReal.ofReal Bt * ENNReal.ofReal Bt * ENNReal.ofReal D) ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hs2, hp _ _ _⟩)
      have h1 := ENNReal.toReal_mono hfin hE
      rw [ENNReal.tsum_toReal_eq (fun n => enorm_ne_top)] at h1
      simp only [toReal_enorm] at h1
      refine h1.trans (le_of_eq ?_)
      rw [ENNReal.toReal_mul, ENNReal.toReal_add hs2 (hp _ _ _), ENNReal.toReal_add (hp _ _ _)
        (hp _ _ _)]
      simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD0, ENNReal.toReal_ofReal hA0,
        ENNReal.toReal_ofReal hB0]
      congr 1
      exact ENNReal.toReal_ofReal (abs_nonneg _)
    have hAle := hWa t ht
    have hBle := hWb t ht
    calc ∑' n, ‖F n t‖ ≤ κ * (D * A * A + Bt * D * A + Bt * Bt * D) := hreal
      _ ≤ κ * (D * (Ca * S) * (Ca * S) + (Cb * S) * D * (Ca * S) + (Cb * S) * (Cb * S) * D) := by
          gcongr
      _ = K * ∑' n, ‖a t n - b t n‖ := by rw [hK]; simp only [D, Pi.sub_apply]; ring
  intro t ht
  have h := key t ht
  simp only [one_mul, ha.1, hb.1, sub_self, norm_zero, tsum_zero, zero_mul] at h
  have hs : Summable fun n => ‖a t n - b t n‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => norm_sub_le _ _)
      ((ha.summable_norm hL ht).add (hb.summable_norm hL ht))
  have hzero : ∑' n, ‖a t n - b t n‖ = 0 := le_antisymm h (tsum_nonneg fun _ => norm_nonneg _)
  have h0 := (hasSum_zero_iff_of_nonneg (fun n => norm_nonneg (a t n - b t n))).1
    (hzero ▸ hs.hasSum)
  funext n
  exact sub_eq_zero.1 (norm_eq_zero.1 (congrFun h0 n))

end Solutions

end WaveTurbulence
