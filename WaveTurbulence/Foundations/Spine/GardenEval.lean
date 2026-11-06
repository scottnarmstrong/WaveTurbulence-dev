/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GardenOps
/-! AMEND6' (design P*): arithmetic and admissibility lemmas for the garden/couple evaluation recursion. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset NormBridgeScratch
open scoped ENNReal

/-- `(1 + y)^n - 1 <= 2 n y` when `n y <= 1/2`. -/
theorem pow_one_add_sub_one_le {y : ℝ} (hy : 0 ≤ y) (n : ℕ) (hny : (n : ℝ) * y ≤ 1 / 2) :
    (1 + y) ^ n - 1 ≤ 2 * n * y := by
  rcases Nat.eq_zero_or_pos n with h0 | h
  · subst h0; simp
  have hy1 : y ≤ 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast h
    nlinarith
  have h1 : 1 - (n : ℝ) * y ≤ (1 - y) ^ n := by
    have := one_add_mul_le_pow (a := -y) (by linarith) n
    simpa [sub_eq_add_neg, mul_neg] using this
  have h2 : (1 + y) ^ n * (1 - y) ^ n ≤ 1 := by
    rw [← mul_pow]
    have : (1 + y) * (1 - y) ≤ 1 := by nlinarith
    exact pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) this
  have hpos : 0 < 1 - (n : ℝ) * y := by linarith
  have h3 : (1 + y) ^ n * (1 - (n : ℝ) * y) ≤ 1 :=
    (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h2
  have : (1 + y) ^ n ≤ 1 + 2 * n * y := by
    by_contra hcon
    push_neg at hcon
    have := mul_lt_mul_of_pos_right hcon hpos
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) hy]
  linarith


theorem AdmI_of_Inv {P : WTParams} {w p : ℕ} {os : List (TOp P.d w)} {u c : ℝ} {g : TProf P.d w}
    (hd : 1 ≤ P.d) (hu : 0 ≤ u) (hc : 0 ≤ c) (h : Inv p (40 * P.d) (40 * P.d) os u c g) : AdmI P p os g := by
  refine ⟨u, c, hu, hc, fun q hq j j' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h q hq j j'
  refine ⟨h1.of_le (by exact_mod_cast (by omega)), ?_, ?_⟩
  · exact SNormR_mono_bound (by omega) (by omega) _ h1 u hu h2
  · exact SNormR_mono_bound (by omega) (by omega) _
      (h1.of_le (by exact_mod_cast Nat.le_add_right _ _)) c hc h3

theorem nodeSign_root_eq {w : ℕ} (sig : Fin w → ℤˣ) (tree : Fin w → TTree) (j : Fin w) :
    nodeSign sig (GNode.root tree j).1 = sig j := by
  simp [nodeSign, TTree.pathSign, GNode.root]

variable {P : WTParams} {w : ℕ} {A : Finset (LayeredGarden w)} {p M : ℕ} {σ : Fin w → ℝ}

theorem garden_weight_identity (hc : EvalCtx P A p M σ) (hσ2 : ∀ j, σ j ^ 2 = 1) (tt : Fin w → ℝ)
    (nroot : Fin w → (Fin P.d → ℤ)) (lam : ℝ) (hlam : lam ≠ 0) (nn : ℕ) (h0 : TProf P.d w)
    (hadm : ∀ c : Fin w → Fin nn → Option (Fin P.d),
      AdmI P p ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0) :
    (((∏ j, jbr (latticePoint P.L (nroot j)) ^ (2 * nn) : ℝ)) : ℂ) * evalV P A tt nroot h0 0 =
      ∑ c : Fin w → Fin nn → Option (Fin P.d),
        evalOps (evalV P A tt nroot) M lam ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 0 := by
  have hterm : ∀ c : Fin w → Fin nn → Option (Fin P.d),
      evalOps (evalV P A tt nroot) M lam ((opsOfChoice c).map fun f => TOp.form f.1 f.2) h0 0 =
        ((∏ j, ∏ t, (c j t).elim (1 : ℝ) (fun i => (latticePoint P.L (nroot j)) i ^ 2) : ℝ) : ℂ) *
          evalV P A tt nroot h0 0 := by
    intro c
    have h := evalV_ders_forms hc tt nroot lam hlam [] (opsOfChoice c) h0 (by simpa using hadm c)
    have h' := congrFun h 0
    simp only [List.map_nil, List.nil_append, List.reverse_nil] at h'
    rw [h', Pi.mul_apply, prod_opsOfChoice (R := Mom P.d → ℂ) c (rootForm P σ nroot)]
    show _ * (wordD [] _ 0) = _
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
      simp only [Option.elim, Pi.pow_apply, rootForm, zero_add]
      push_cast
      have : ((σ j : ℂ)) ^ 2 = 1 := by exact_mod_cast hσ2 j
      rw [mul_pow, this, one_mul]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← prod_jbr_pow_expand (fun j => latticePoint P.L (nroot j)) nn]

end WaveTurbulence.LGSpine
