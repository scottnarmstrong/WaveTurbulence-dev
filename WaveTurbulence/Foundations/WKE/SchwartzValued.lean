/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKE.Leibniz
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The collision operator maps Schwartz functions to Schwartz functions

For `d ≥ 2` and Schwartz inputs, each term `𝒦ⱼ(φ₁, φ₂, φ₃)` and `𝒦 = collisionOp` is a Schwartz
function (`collisionTermSchwartz`, `collisionOpSchwartz`). Smoothness follows by iterating the
Leibniz rule (`hasFDerivAt_collisionTerm`), whose derivative is again a sum of `𝒦ⱼ`'s of
Schwartz functions; decay of every derivative follows from the weighted-sup trilinear estimate
(`abs_collisionTerm_le`, a weighted-`L^∞` estimate, not the `L²_s` estimate (schappend8)). This
plays the role of the `Z_{s,m}` mapping property used in TARGET Appendix C (L2526).
-/

public section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace SchwartzMap LineDeriv

namespace WaveTurbulence

variable {d : ℕ}

/-- The directional derivative `∂ᵥφ` of a Schwartz function, as a Schwartz function. -/
@[expose] noncomputable def partialSchwartz (v : Mom d) (φ : 𝓢(Mom d, ℝ)) : 𝓢(Mom d, ℝ) :=
  ∂_{v} φ

theorem partialSchwartz_apply (v : Mom d) (φ : 𝓢(Mom d, ℝ)) (y : Mom d) :
    partialSchwartz v φ y = fderiv ℝ φ y v := rfl

theorem fderiv_collisionTerm (hd : 2 ≤ d) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) (j : Fin 4) (k v : Mom d) :
    fderiv ℝ (collisionTerm j φ₁ φ₂ φ₃) k v =
      collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃ k + collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃ k
        + collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃) k := by
  obtain ⟨L, hL, hLv⟩ := hasFDerivAt_collisionTerm hd φ₁ φ₂ φ₃ j k
  rw [hL.fderiv, hLv]
  rfl

theorem differentiable_collisionTerm (hd : 2 ≤ d) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) (j : Fin 4) :
    Differentiable ℝ (collisionTerm j φ₁ φ₂ φ₃) := fun k =>
  (hasFDerivAt_collisionTerm hd φ₁ φ₂ φ₃ j k).choose_spec.1.differentiableAt

theorem contDiff_collisionTerm (hd : 2 ≤ d) (j : Fin 4) :
    ∀ n : ℕ, ∀ φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ), ContDiff ℝ n (collisionTerm j φ₁ φ₂ φ₃)
  | 0 => fun φ₁ φ₂ φ₃ => contDiff_zero.mpr (differentiable_collisionTerm hd φ₁ φ₂ φ₃ j).continuous
  | n + 1 => fun φ₁ φ₂ φ₃ => by
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
        contDiff_succ_iff_fderiv]
      refine ⟨differentiable_collisionTerm hd φ₁ φ₂ φ₃ j, fun h => absurd h (by simp), ?_⟩
      rw [contDiff_clm_apply_iff]
      intro v
      have e : (fun k => fderiv ℝ (collisionTerm j φ₁ φ₂ φ₃) k v) = fun k =>
          collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃ k + collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃ k
            + collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃) k :=
        funext fun k => fderiv_collisionTerm hd φ₁ φ₂ φ₃ j k v
      rw [e]
      exact ((contDiff_collisionTerm hd j n _ _ _).add (contDiff_collisionTerm hd j n _ _ _)).add
        (contDiff_collisionTerm hd j n _ _ _)

theorem contDiff_infty_collisionTerm (hd : 2 ≤ d) (j : Fin 4) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (collisionTerm j φ₁ φ₂ φ₃) :=
  contDiff_infty.mpr fun n => contDiff_collisionTerm hd j n φ₁ φ₂ φ₃

/-- `‖S‖ ≤ Σ_b |S e_b|` for a linear functional on `ℝ^d`. -/
theorem norm_clm_le_sum_basis (S : Mom d →L[ℝ] ℝ) :
    ‖S‖ ≤ ∑ b : Fin d, |S (EuclideanSpace.single b 1)| := by
  refine S.opNorm_le_bound (Finset.sum_nonneg fun b _ => abs_nonneg _) fun v => ?_
  have hv : v = ∑ b : Fin d, v b • EuclideanSpace.single b (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
    simp
  calc ‖S v‖ = |∑ b : Fin d, v b * S (EuclideanSpace.single b 1)| := by
        conv_lhs => rw [hv]
        simp [map_sum, map_smul, Real.norm_eq_abs]
    _ ≤ ∑ b : Fin d, |v b| * |S (EuclideanSpace.single b 1)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
        simp [abs_mul]
    _ ≤ ∑ b : Fin d, ‖v‖ * |S (EuclideanSpace.single b 1)| := by
        gcongr with b
        rw [← Real.norm_eq_abs]
        exact PiLp.norm_apply_le v b
    _ = (∑ b : Fin d, |S (EuclideanSpace.single b 1)|) * ‖v‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => mul_comm _ _

/-- The norm of an iterated derivative of a linear-functional-valued map, by components. -/
theorem norm_iteratedFDeriv_le_sum_basis {c : Mom d → Mom d →L[ℝ] ℝ} {n : ℕ}
    (hc : ContDiff ℝ n c) (x : Mom d) :
    ‖iteratedFDeriv ℝ n c x‖ ≤
      ∑ b : Fin d, ‖iteratedFDeriv ℝ n (fun y => c y (EuclideanSpace.single b 1)) x‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun b _ => norm_nonneg _) fun m => ?_
  refine (norm_clm_le_sum_basis _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [← iteratedFDeriv_clm_apply_const_apply hc le_rfl, ← Real.norm_eq_abs]
  exact ContinuousMultilinearMap.le_opNorm _ m

theorem decay_collisionTerm (hd : 2 ≤ d) (j : Fin 4) :
    ∀ n : ℕ, ∀ φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ), ∀ m : ℕ, ∃ C : ℝ, ∀ x : Mom d,
      ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (collisionTerm j φ₁ φ₂ φ₃) x‖ ≤ C
  | 0 => fun φ₁ φ₂ φ₃ m => by
      set s : ℝ := (m : ℝ) + 2 * d + 1
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hs : 2 * (d : ℝ) < s := by simp only [s]; linarith
      obtain ⟨C₁, -, b₁⟩ := exists_norm_le_of_schwartz φ₁ s
      obtain ⟨C₂, -, b₂⟩ := exists_norm_le_of_schwartz φ₂ s
      obtain ⟨C₃, -, b₃⟩ := exists_norm_le_of_schwartz φ₃ s
      have D := fun (φ : 𝓢(Mom d, ℝ)) {C : ℝ} (h : ∀ y, ‖φ y‖ ≤ C * (1 + ‖y‖) ^ (-s)) =>
        (fun y => by rw [← Real.norm_eq_abs]; exact h y : DecayBound C s φ)
      refine ⟨3 * tameConst d s * 3 ^ s * (C₁ * C₂ * C₃), fun x => ?_⟩
      have h := abs_collisionTerm_le hd hs (D φ₁ b₁) (D φ₂ b₂) (D φ₃ b₃) j x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have hx : ‖x‖ ^ m ≤ (1 + ‖x‖) ^ s := by
        calc ‖x‖ ^ m ≤ (1 + ‖x‖) ^ m := pow_le_pow_left₀ (norm_nonneg x) (by linarith) m
          _ = (1 + ‖x‖) ^ (m : ℝ) := (Real.rpow_natCast _ m).symm
          _ ≤ (1 + ‖x‖) ^ s := Real.rpow_le_rpow_of_exponent_le
              (by linarith [norm_nonneg x])
              (by simp only [s]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
      exact (mul_le_mul_of_nonneg_right hx (abs_nonneg _)).trans h
  | n + 1 => fun φ₁ φ₂ φ₃ m => by
      have hc : ContDiff ℝ n (fderiv ℝ (collisionTerm j φ₁ φ₂ φ₃)) := by
        have := contDiff_collisionTerm hd j (n + 1) φ₁ φ₂ φ₃
        rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
          contDiff_succ_iff_fderiv] at this
        exact this.2.2
      have hb : ∀ b : Fin d, ∃ C : ℝ, ∀ x : Mom d, ‖x‖ ^ m *
          ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ (collisionTerm j φ₁ φ₂ φ₃) y
            (EuclideanSpace.single b 1)) x‖ ≤ C := by
        intro b
        set v : Mom d := EuclideanSpace.single b 1
        have e : (fun y => fderiv ℝ (collisionTerm j φ₁ φ₂ φ₃) y v) = fun y =>
            collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃ y + collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃ y
              + collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃) y :=
          funext fun y => fderiv_collisionTerm hd φ₁ φ₂ φ₃ j y v
        rw [e]
        obtain ⟨A₁, hA₁⟩ := decay_collisionTerm hd j n (partialSchwartz v φ₁) φ₂ φ₃ m
        obtain ⟨A₂, hA₂⟩ := decay_collisionTerm hd j n φ₁ (partialSchwartz v φ₂) φ₃ m
        obtain ⟨A₃, hA₃⟩ := decay_collisionTerm hd j n φ₁ φ₂ (partialSchwartz v φ₃) m
        have c₁ := contDiff_collisionTerm hd j n (partialSchwartz v φ₁) φ₂ φ₃
        have c₂ := contDiff_collisionTerm hd j n φ₁ (partialSchwartz v φ₂) φ₃
        have c₃ := contDiff_collisionTerm hd j n φ₁ φ₂ (partialSchwartz v φ₃)
        refine ⟨A₁ + A₂ + A₃, fun x => ?_⟩
        have hsplit : iteratedFDeriv ℝ n (fun y => collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃ y
            + collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃ y + collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃) y) x =
            iteratedFDeriv ℝ n (collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃) x
              + iteratedFDeriv ℝ n (collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃) x
              + iteratedFDeriv ℝ n (collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃)) x := by
          change iteratedFDeriv ℝ n ((collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃
            + collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃)
            + collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃)) x = _
          have c₁₂ : ContDiff ℝ n (collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃
              + collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃) := c₁.add c₂
          rw [iteratedFDeriv_add_apply c₁₂.contDiffAt c₃.contDiffAt,
            iteratedFDeriv_add_apply c₁.contDiffAt c₂.contDiffAt]
        rw [hsplit]
        have t : ‖iteratedFDeriv ℝ n (collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃) x
            + iteratedFDeriv ℝ n (collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃) x
            + iteratedFDeriv ℝ n (collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃)) x‖ ≤
            ‖iteratedFDeriv ℝ n (collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃) x‖
            + ‖iteratedFDeriv ℝ n (collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃) x‖
            + ‖iteratedFDeriv ℝ n (collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃)) x‖ :=
          norm_add₃_le
        have hm := pow_nonneg (norm_nonneg x) m
        calc ‖x‖ ^ m * ‖_‖ ≤ ‖x‖ ^ m * (‖iteratedFDeriv ℝ n (collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃) x‖
              + ‖iteratedFDeriv ℝ n (collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃) x‖
              + ‖iteratedFDeriv ℝ n (collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃)) x‖) :=
            mul_le_mul_of_nonneg_left t hm
          _ ≤ A₁ + A₂ + A₃ := by
            have := hA₁ x; have := hA₂ x; have := hA₃ x
            linarith [mul_add (‖x‖ ^ m) (‖iteratedFDeriv ℝ n (collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃) x‖
              + ‖iteratedFDeriv ℝ n (collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃) x‖)
              ‖iteratedFDeriv ℝ n (collisionTerm j φ₁ φ₂ (partialSchwartz v φ₃)) x‖,
              mul_add (‖x‖ ^ m) ‖iteratedFDeriv ℝ n (collisionTerm j (partialSchwartz v φ₁) φ₂ φ₃) x‖
              ‖iteratedFDeriv ℝ n (collisionTerm j φ₁ (partialSchwartz v φ₂) φ₃) x‖]
      choose C hC using hb
      refine ⟨∑ b : Fin d, C b, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv]
      have hm := pow_nonneg (norm_nonneg x) m
      calc ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (fderiv ℝ (collisionTerm j φ₁ φ₂ φ₃)) x‖
          ≤ ‖x‖ ^ m * ∑ b : Fin d, ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ
              (collisionTerm j φ₁ φ₂ φ₃) y (EuclideanSpace.single b 1)) x‖ :=
            mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_le_sum_basis hc x) hm
        _ = ∑ b : Fin d, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ
              (collisionTerm j φ₁ φ₂ φ₃) y (EuclideanSpace.single b 1)) x‖ := Finset.mul_sum _ _ _
        _ ≤ ∑ b : Fin d, C b := Finset.sum_le_sum fun b _ => hC b x

/-- The term `𝒦ⱼ(φ₁, φ₂, φ₃)` as a Schwartz function (`d ≥ 2`). -/
@[expose] noncomputable def collisionTermSchwartz (hd : 2 ≤ d) (j : Fin 4)
    (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) : 𝓢(Mom d, ℝ) where
  toFun := collisionTerm j φ₁ φ₂ φ₃
  smooth' := contDiff_infty_collisionTerm hd j φ₁ φ₂ φ₃
  decay' k n := decay_collisionTerm hd j n φ₁ φ₂ φ₃ k

@[simp] theorem coe_collisionTermSchwartz (hd : 2 ≤ d) (j : Fin 4) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) :
    ⇑(collisionTermSchwartz hd j φ₁ φ₂ φ₃) = collisionTerm j φ₁ φ₂ φ₃ := rfl

/-- **`𝒦` maps `𝓢³` to `𝓢`**: `collisionOp φ₁ φ₂ φ₃` as a Schwartz function (`d ≥ 2`). -/
@[expose] noncomputable def collisionOpSchwartz (hd : 2 ≤ d) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) :
    𝓢(Mom d, ℝ) :=
  collisionTermSchwartz hd 0 φ₁ φ₂ φ₃ - collisionTermSchwartz hd 1 φ₁ φ₂ φ₃
    + collisionTermSchwartz hd 2 φ₁ φ₂ φ₃ - collisionTermSchwartz hd 3 φ₁ φ₂ φ₃

theorem coe_collisionOpSchwartz (hd : 2 ≤ d) (φ₁ φ₂ φ₃ : 𝓢(Mom d, ℝ)) :
    ⇑(collisionOpSchwartz hd φ₁ φ₂ φ₃) = collisionOp φ₁ φ₂ φ₃ := by
  funext k
  obtain ⟨C, hC⟩ := collisionInputs_of_schwartz φ₁ φ₂ φ₃ (by linarith : 2 * (d : ℝ) < 2 * d + 1)
  rw [collisionOp_eq_sum hC hd k]
  simp [collisionOpSchwartz]

end WaveTurbulence
