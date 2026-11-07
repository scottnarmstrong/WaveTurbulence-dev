/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GardenEval
/-! AMEND-ST3 (R69 (b)): the garden weight identity at an arbitrary base momentum `k` (weights
`jbr(k + n_j / L)`); `garden_weight_identity` is the case `k = 0` (`garden_weight_identity_zero`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset NormBridgeScratch
open scoped ENNReal

variable {P : WTParams} {w : ℕ} {A : Finset (LayeredGarden w)} {p M : ℕ} {σ : Fin w → ℝ}

theorem garden_weight_identity_at (hc : EvalCtx P A p M σ) (hσ2 : ∀ j, σ j ^ 2 = 1) (tt : Fin w → ℝ)
    (nroot : Fin w → (Fin P.d → ℤ)) (k : Mom P.d) (lam : ℝ) (hlam : lam ≠ 0) (nn : ℕ) (h0 : TProf P.d w)
    (hadm : ∀ c : Fin w → Fin nn → Option (Fin P.d),
      AdmI P p ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0) :
    (((∏ j, jbr (k + latticePoint P.L (nroot j)) ^ (2 * nn) : ℝ)) : ℂ) * evalV P A tt nroot h0 k =
      ∑ c : Fin w → Fin nn → Option (Fin P.d),
        evalOps (evalV P A tt nroot) M lam ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 k := by
  have hterm : ∀ c : Fin w → Fin nn → Option (Fin P.d),
      evalOps (evalV P A tt nroot) M lam ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 k =
        ((∏ j, ∏ t, (c j t).elim (1 : ℝ) (fun i => (k + latticePoint P.L (nroot j)) i ^ 2) : ℝ) : ℂ) *
          evalV P A tt nroot h0 k := by
    intro c
    have h := evalV_ders_forms hc tt nroot lam hlam [] (opsOfChoice c) h0 (by simpa using hadm c)
    have h' := congrFun h k
    simp only [List.map_nil, List.nil_append, List.reverse_nil] at h'
    rw [h', Pi.mul_apply, prod_opsOfChoice (R := Mom P.d → ℂ) c (rootForm P σ nroot)]
    show _ * (wordD [] _ k) = _
    simp only [wordD]
    congr 1
    rw [Finset.prod_apply]
    push_cast
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Finset.prod_apply]
    refine Finset.prod_congr rfl fun t _ => ?_
    cases c j t with
    | none => simp
    | some i =>
      simp only [Option.elim, Pi.pow_apply, rootForm]
      push_cast
      have : ((σ j : ℂ)) ^ 2 = 1 := by exact_mod_cast hσ2 j
      rw [mul_pow, this, one_mul]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← prod_jbr_pow_expand (fun j => k + latticePoint P.L (nroot j)) nn]


/-- **Bridge**: the base-`k` identity at `k = 0` is `garden_weight_identity`. -/
theorem garden_weight_identity_zero (hc : EvalCtx P A p M σ) (hσ2 : ∀ j, σ j ^ 2 = 1) (tt : Fin w → ℝ)
    (nroot : Fin w → (Fin P.d → ℤ)) (lam : ℝ) (hlam : lam ≠ 0) (nn : ℕ) (h0 : TProf P.d w)
    (hadm : ∀ c : Fin w → Fin nn → Option (Fin P.d),
      AdmI P p ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0) :
    (((∏ j, jbr (latticePoint P.L (nroot j)) ^ (2 * nn) : ℝ)) : ℂ) * evalV P A tt nroot h0 0 =
      ∑ c : Fin w → Fin nn → Option (Fin P.d),
        evalOps (evalV P A tt nroot) M lam ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 0 := by
  have := garden_weight_identity_at hc hσ2 tt nroot 0 lam hlam nn h0 hadm
  simpa only [zero_add] using this

end WaveTurbulence.LGSpine
