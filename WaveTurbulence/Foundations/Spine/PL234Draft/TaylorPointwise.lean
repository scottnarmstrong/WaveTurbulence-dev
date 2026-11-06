/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.TaylorInputs
public import WaveTurbulence.Foundations.Spine.PL234Draft.WeightedPointwise
public import WaveTurbulence.Foundations.Spine.LeafwisePointwise
public import WaveTurbulence.Foundations.XChain.SNormPointwise
public import WaveTurbulence.Foundations.RegularAsymptotics.RegularAppContinuity

/-!
# TARGET Prop 6.2: pointwise consequences of the single-layer estimates

At a time point of the closed box the norm estimates of B2.1 give pointwise bounds:

* `norm_le_of_XNormRestr`: weighted pointwise control `‖F(t, k)‖ ≤ e ⟨k⟩^{-B}` from
  `‖F‖_{𝔛^{θ,A,B}} ≤ e` (only the zeroth multi-index is used);
* `abs_JB_le`: the time factor `J_B` of a couple code from its `𝔛^{1-η}` bound (B2.1 (3));
* `norm_LeafApp_couple_le`: the leading term of a couple code of size `2n`,
  `‖𝒜(t, s, k)‖ ≤ δ^n 2^n c_J c_M ⟨k⟩^{-30d}`, from bounds `c_J` on `J_B` and `c_M` on the momentum
  factors `ℳ*` (TARGET (regref1-3)).
-/

@[expose] public section
open WaveTurbulence.Induct

open MeasureTheory Set Finset
open scoped ENNReal

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

/-- A weighted bound `⟨k⟩^B x ≤ e` is the bound `x ≤ e ⟨k⟩^{-B}`. -/
theorem le_mul_jbr_neg_of_weight {d : ℕ} (k : Mom d) (B : ℕ) {x e : ℝ} (h : jbr k ^ B * x ≤ e) :
    x ≤ e * jbr k ^ (-(B : ℝ)) := by
  have hpos : 0 < jbr k ^ B := pow_pos (jbr_pos k) B
  rw [Real.rpow_neg (jbr_pos k).le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith [mul_comm x (jbr k ^ B)]

/-- **Pointwise control from the restriction norm** at a point of the closed box, for a function
continuous in time. -/
theorem norm_le_of_XNormRestr {r d : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (A B : ℕ) (T : Set (Fin r → ℝ))
    (F : (Fin r → ℝ) → Mom d → ℂ) (t : Fin r → ℝ) (k : Mom d)
    (ht : t ∈ closure (interior T)) (hc : Continuous (fun s => F s k)) {e : ℝ} (he : 0 ≤ e)
    (hX : XNormRestr θ A B T Set.univ F ≤ ENNReal.ofReal e) :
    ‖F t k‖ ≤ e * jbr k ^ (-(B : ℝ)) := by
  have h := (enorm_weight_le_XNormRestr_of_continuous hθ A B T Set.univ F t k ht (mem_univ k)
    hc).trans hX
  exact le_mul_jbr_neg_of_weight k B ((ENNReal.ofReal_le_ofReal_iff he).mp h)

/-- **The time factor of a couple code** is bounded pointwise on the closed box by its `𝔛^{1-η}`
bound (B2.1 (3)). -/
theorem abs_JB_le {η : ℝ} (hη : η ≤ 1) (Q : RegCpl) (r : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hX : XNorm00Restr (V := Unit) (1 - η) (timeBox r r) Set.univ
      (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal c)
    {t s : ℝ} (ht : t ∈ Icc (r : ℝ) (r + 1)) (hs : s ∈ Icc (r : ℝ) (r + 1)) :
    |Q.JB r t s| ≤ c := by
  have hu : Continuous (fun ts : Fin 2 → ℝ => (ts 0, ts 1)) :=
    (continuous_apply 0).prodMk (continuous_apply 1)
  have hJc : Continuous (fun ts : Fin 2 → ℝ => Q.JB r (ts 0) (ts 1)) :=
    (continuous_RegCpl_JB r Q).comp hu
  have hcont : Continuous (fun ts : Fin 2 → ℝ => (Q.JB r (ts 0) (ts 1) : ℂ)) :=
    Complex.continuous_ofReal.comp hJc
  have htime : ![t, s] ∈ closure (interior (timeBox (r : ℝ) r)) := by
    rw [closure_interior_timeBox]
    exact ⟨ht, hs⟩
  have h := enorm_le_mixedRestrictionNorm00_closure_interior (by linarith : (0 : ℝ) ≤ 1 - η)
    (timeBox (r : ℝ) r) (Set.univ : Set Unit) (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ![t, s] ()
    htime (mem_univ _) hcont
  have hb := NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00 (V := Unit) (1 - η)
    (timeBox (r : ℝ) r) Set.univ (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ))
  have h2 := (h.trans hb.symm.le).trans hX
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hc] at h2
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real,
    Real.norm_eq_abs] using h2

/-- **The leading term of a couple code is bounded pointwise** by its factors (TARGET (regref1-3)):
`‖𝒜_𝒬(t, s, k)‖ ≤ δ^n 2^n c_J c_M ⟨k⟩^{-30d}` for a code of size `2n`. -/
theorem norm_LeafApp_couple_le {d : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (r : ℕ) (H : LeafProfiles 2 d)
    (Q : RegCpl) {n : ℕ} (hsize : Q.size = 2 * n) (t s : ℝ) (k : Mom d) {cJ cM : ℝ}
    (hcJ : 0 ≤ cJ) (hcM : 0 ≤ cM) (hJ : Q.dominant = true → |Q.JB r t s| ≤ cJ)
    (hM : Q.dominant = true → ∀ Z ∈ specialSets Q.links,
      SNormR (30 * d) (30 * d) (LeafApp.cplMstar H Z Q (0, []) (1, [])) ≤ ENNReal.ofReal cM) :
    ‖LeafApp.couple δ r H Q t s k‖ ≤ δ ^ n * 2 ^ n * cJ * cM * jbr k ^ (-(30 * d : ℝ)) := by
  have hj : 0 ≤ jbr k ^ (-(30 * d : ℝ)) := Real.rpow_nonneg (jbr_pos k).le _
  unfold LeafApp.couple
  split_ifs with hdom
  · rw [norm_mul]
    have hcoef : ‖(2 : ℂ)⁻¹ ^ Q.size * (δ : ℂ) ^ (Q.size / 2) *
        zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2]‖ ≤ δ ^ n := by
      rw [norm_mul, norm_mul, norm_zetaOfTrees, mul_one, norm_pow, norm_pow, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg hδ, hsize, Nat.mul_div_cancel_left n two_pos]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      have h1 : (2⁻¹ : ℝ) ^ (2 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      calc (2⁻¹ : ℝ) ^ (2 * n) * δ ^ n ≤ 1 * δ ^ n :=
            mul_le_mul_of_nonneg_right h1 (pow_nonneg hδ n)
        _ = δ ^ n := one_mul _
    have hterm : ∀ Z ∈ specialSets Q.links,
        ‖specialWeight ![1, -1] Z * (Q.JB r t s : ℂ) *
          (LeafApp.cplMstar H Z Q (0, []) (1, []) k : ℂ)‖ ≤
          cJ * (cM * jbr k ^ (-(30 * d : ℝ))) := by
      intro Z hZ
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hw := norm_specialWeight_le ![1, -1] Z
      have hJ' := hJ hdom
      have hM' := SNormR_pointwise _ cM hcM (hM hdom Z hZ) k
      have hcast : ((30 * d : ℕ) : ℝ) = 30 * (d : ℝ) := by push_cast; ring
      rw [hcast] at hM'
      calc ‖specialWeight ![1, -1] Z‖ * |Q.JB r t s| * |LeafApp.cplMstar H Z Q (0, []) (1, []) k|
          ≤ 1 * cJ * (cM * jbr k ^ (-(30 * d : ℝ))) := by
            apply mul_le_mul (mul_le_mul hw hJ' (abs_nonneg _) zero_le_one) hM' (abs_nonneg _)
            positivity
        _ = cJ * (cM * jbr k ^ (-(30 * d : ℝ))) := by ring
    have hsum : ‖∑ Z ∈ specialSets Q.links, specialWeight ![1, -1] Z * (Q.JB r t s : ℂ) *
        (LeafApp.cplMstar H Z Q (0, []) (1, []) k : ℂ)‖ ≤
          2 ^ n * (cJ * (cM * jbr k ^ (-(30 * d : ℝ)))) := by
      apply (norm_sum_le _ _).trans
      apply (Finset.sum_le_card_nsmul _ _ _ hterm).trans
      rw [nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_specialSets_couple_le hsize
    calc _ ≤ δ ^ n * (2 ^ n * (cJ * (cM * jbr k ^ (-(30 * d : ℝ))))) :=
          mul_le_mul hcoef hsum (norm_nonneg _) (pow_nonneg hδ n)
      _ = δ ^ n * 2 ^ n * cJ * cM * jbr k ^ (-(30 * d : ℝ)) := by ring
  · rw [norm_zero]
    positivity

end WaveTurbulence.PL234
