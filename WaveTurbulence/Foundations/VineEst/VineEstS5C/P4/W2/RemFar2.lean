/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemFar1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.ZpObj
public import WaveTurbulence.Foundations.Spine.PL2330Draft.Step
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BoxFacts

/-! # P4-W2 (session 8, R-SUPPLY): the remainders above the gate level, and the face trace of restriction norms

`remQ_eq_clamp`, `remT_eq_clamp`: for `t > q` and a coherent carrier at `(q, L₂)`, `remQ κ (zpQfam κ A) b t s k` is the gate remainder `K* - SourceApp` evaluated at
`(min t (q+1), s)`: the approximant is the constant extension (`zpQfam_eq_clamp`) and the exact kernel is time-constant beyond `q + 1`
(`KQstar_const_above`, all layers `≤ q`).  `xnormRestr_face_trace`: the trace of a time-continuous function at the face `t = q + 1` of a box, as a bound for the
restriction norm `XNormRestr θ Λ Λ₂` with `Λ ≠ 0`, through the exact bridge `XNormRestr = rN` (`PL2330.rN_trace_transport`). -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4.W13
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.ZpSurj

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} {d : ℕ} [Fintype ι] [DecidableEq ι]
  (κ : KPar d) (A : FamilyReconstruction w ι) (b : ST w ι pstar J)

theorem remQ_eq_clamp {q : ℕ} (hL2q : zpQ2 A pstar ≤ q) (hqp : q ≤ p)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar)) {t : ℝ} (ht : (q : ℝ) < t)
    (s : ℝ) (k : Mom d) :
    remQ κ (zpQfam κ A) b t s k =
      KQstar κ.L κ.γ κ.δ κ.F (zpObjC b.1 pstar) (min t (q + 1)) s k -
        SourceApp.couple κ.δ κ.F (zpObjC b.1 pstar) (zpCodeC b.1 pstar) q (zpQ2 A pstar) (min t (q + 1)) s k := by
  unfold remQ
  rw [zpQfam_eq_clamp κ A b hL2q hqp hcoh ht s k]
  congr 1
  rcases le_total t ((q : ℝ) + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    exact KQstar_const_above _ _ _ _ _ (fun bb _ => coherentCouple_layer_le_q hL2q hqp hcoh bb.toNode) h le_rfl s k

theorem remT_eq_clamp {q : ℕ} (hL2q : zpQ2 A pstar ≤ q)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar)) {t : ℝ} (ht : (q : ℝ) < t)
    (s : ℝ) (k : Mom d) :
    remT κ (zpTfam κ A) b t s k =
      KTstar κ.L κ.γ κ.δ κ.F (zpObjT b.1 pstar) (min t (q + 1)) s k -
        SourceApp.tree κ.δ κ.F (zpObjT b.1 pstar) (zpCodeT b.1 pstar) q (zpQ2 A pstar) (min t (q + 1)) s k := by
  unfold remT
  rw [zpTfam_eq_clamp κ A b hL2q hcoh ht s k]
  congr 1
  rcases le_total t ((q : ℝ) + 1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    exact KTstar_const_above _ _ _ _ _ (fun bb => (coherentTree_layer_le hL2q hcoh bb.toNode)) h le_rfl s k

end WaveTurbulence.VineEstS5C.P4.W2

namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.PL2330 WaveTurbulence.Regref MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

theorem xnormRestr_face_trace {θ : ℝ} (hθ : 0 ≤ θ) {Λ Λ₂ : ℕ} (hΛ : Λ ≠ 0) (g : (Fin 2 → ℝ) → Mom d → ℂ)
    (hg : ∀ k, Continuous fun ts => g ts k) (q q2 w : ℝ) {Bn Bw : Set (Fin 2 → ℝ)}
    (hBw : ∀ t ∈ Bw, t 0 ∈ Icc w (w + 1) ∧ t 1 ∈ Icc q2 (q2 + 1))
    (hBn : ∀ s ∈ Icc q2 (q2 + 1), ![q + 1, s] ∈ closure (interior Bn)) :
    XNormRestr θ Λ Λ₂ Bw Set.univ (fun ts k => g ![q + 1, ts 1] k) ≤
      Regref.traceConst (r := 2) θ Layered.chiUnit * XNormRestr θ Λ Λ₂ Bn Set.univ g := by
  rw [XNormRestr_eq_rN, XNormRestr_eq_rN]
  have hfun : (fun (ts : Fin 2 → ℝ) (k : Mom d) => g ![q + 1, ts 1] k) =
      fun t k => g (Function.update (t + ![-w, -q2]) 0 1 + ![q, q2]) k := by
    funext t k
    congr 1
    funext i
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail] <;> ring
  rw [hfun]
  refine rN_trace_transport (d := d) (θ := θ) (Λ := Λ) (Λ₂ := Λ₂) hΛ hθ (B := Bn) (T' := Bw)
    g hg ![q, q2] ![-w, -q2] 0 1 ?_ ?_
  · intro t ht i
    obtain ⟨⟨h0, h0'⟩, ⟨h1, h1'⟩⟩ := hBw t ht
    fin_cases i
    · simp only [Fin.zero_eta, Pi.add_apply, Matrix.cons_val_zero]
      constructor <;> linarith
    · simp only [Fin.mk_one, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
      constructor <;> linarith
  · intro u hu
    have h1 := hu 1
    have := hBn (u 1 + q2) ⟨by linarith [h1.1], by linarith [h1.2]⟩
    convert this using 2
    funext i
    fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail] <;> ring

end WaveTurbulence.VineEstS5C.P4.W2
