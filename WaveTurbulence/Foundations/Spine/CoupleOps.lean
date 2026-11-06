/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.GardenEval
/-! AMEND6' (design P*): the root-weight choices of a COUPLE (one tree `j0` only: `jbr(k)^{2 nn}`), their operation
lists, counts, and the weight identity `jbr(x)^{2nn} * wordD word (V h) (x) = sum_c evalOps (word.reverse ders ++ forms c)`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset NormBridgeScratch

/-- Two root forms `M^{(j0)}_i` for each chosen coordinate. -/
@[expose] def opsOfChoice0 {d w nn : ℕ} (j0 : Fin w) (c : Fin nn → Option (Fin d)) : List (Fin w × Fin d) :=
  (List.finRange nn).flatMap fun t =>
    match c t with
    | none => []
    | some i => [(j0, i), (j0, i)]

theorem prod_opsOfChoice0 {d w nn : ℕ} {R : Type*} [CommRing R] (j0 : Fin w) (c : Fin nn → Option (Fin d))
    (fv : Fin w → Fin d → R) :
    ((opsOfChoice0 j0 c).map fun f => fv f.1 f.2).prod = ∏ t, (c t).elim 1 (fun i => fv j0 i ^ 2) := by
  unfold opsOfChoice0
  rw [List.map_flatMap, prod_flatMap_aux, ← Fin.prod_univ_def]
  refine Finset.prod_congr rfl fun t _ => ?_
  cases c t <;> simp [sq]

theorem fcnt_opsOfChoice0 {d w nn : ℕ} (j0 : Fin w) (c : Fin nn → Option (Fin d)) (j j' : Fin w) :
    fcnt j j' ((opsOfChoice0 j0 c).map fun f => TOp.form f.1 f.2) ≤ 2 * nn := by
  rw [fcnt_forms]
  unfold opsOfChoice0
  rw [List.map_flatMap, sum_flatMap_aux, ← Fin.sum_univ_def]
  calc _ ≤ ∑ t : Fin nn, 2 := by
        refine Finset.sum_le_sum fun t _ => ?_
        cases c t <;> simp [nzForm] <;> split_ifs <;> omega
    _ = 2 * nn := by simp [mul_comm]

theorem length_opsOfChoice0_le {d w nn : ℕ} (j0 : Fin w) (c : Fin nn → Option (Fin d)) :
    (opsOfChoice0 j0 c).length ≤ 2 * nn := by
  unfold opsOfChoice0
  rw [List.length_flatMap]
  have := List.sum_le_length_nsmul ((List.finRange nn).map fun t => (match c t with
      | none => []
      | some i => [(j0, i), (j0, i)]).length) 2 (by
        intro x hx
        obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx
        cases c t <;> simp)
  simp only [List.length_map, List.length_finRange, smul_eq_mul] at this
  calc _ ≤ nn * 2 := this
    _ = _ := by ring

theorem dcnt_append {d w : ℕ} (a b : List (TOp d w)) : dcnt (a ++ b) = dcnt a + dcnt b := by
  simp [dcnt, List.map_append, List.sum_append]

theorem fcnt_append {d w : ℕ} (j j' : Fin w) (a b : List (TOp d w)) :
    fcnt j j' (a ++ b) = fcnt j j' a + fcnt j j' b := by
  simp [fcnt, List.map_append, List.sum_append]

theorem dcnt_ders {d w : ℕ} (ders : List (Fin d)) : dcnt (ders.map (TOp.der (w := w))) = ders.length := by
  have : ∀ i : Fin d, TOp.dc (TOp.der (w := w) i) = 1 := fun _ => rfl
  simp [dcnt, List.map_map, Function.comp_def, this]

theorem fcnt_ders {d w : ℕ} (j j' : Fin w) (ders : List (Fin d)) :
    fcnt j j' (ders.map (TOp.der (w := w))) = 0 := by
  have : ∀ i : Fin d, TOp.fc j j' (TOp.der (w := w) i) = 0 := fun _ => rfl
  simp [fcnt, List.map_map, Function.comp_def, this]

variable {P : WTParams} {w : ℕ} {A : Finset (LayeredGarden w)} {p M : ℕ} {σ : Fin w → ℝ}

theorem couple_weight_identity (hc : EvalCtx P A p M σ) (j0 : Fin w) (hσ2 : σ j0 ^ 2 = 1)
    (tt : Fin w → ℝ) (nroot : Fin w → (Fin P.d → ℤ)) (h0n : nroot j0 = fun _ => 0)
    (lam : ℝ) (hlam : lam ≠ 0) (nn : ℕ) (h0 : TProf P.d w) (word : List (Fin P.d)) (x : Mom P.d)
    (hadm : ∀ c : Fin nn → Option (Fin P.d),
      AdmI P p (word.reverse.map TOp.der ++ (opsOfChoice0 j0 c).map fun f => TOp.form f.1 f.2) h0) :
    ((jbr x ^ (2 * nn) : ℝ) : ℂ) * wordD word (evalV P A tt nroot h0) x =
      ∑ c : Fin nn → Option (Fin P.d),
        evalOps (evalV P A tt nroot) M lam
          (word.reverse.map TOp.der ++ (opsOfChoice0 j0 c).map fun f => TOp.form f.1 f.2) h0 x := by
  have hterm : ∀ c : Fin nn → Option (Fin P.d),
      evalOps (evalV P A tt nroot) M lam
          (word.reverse.map TOp.der ++ (opsOfChoice0 j0 c).map fun f => TOp.form f.1 f.2) h0 x =
        ((∏ t, (c t).elim (1 : ℝ) (fun i => x i ^ 2) : ℝ) : ℂ) * wordD word (evalV P A tt nroot h0) x := by
    intro c
    have h := evalV_ders_forms hc tt nroot lam hlam word.reverse (opsOfChoice0 j0 c) h0 (hadm c)
    rw [h, List.reverse_reverse, Pi.mul_apply, prod_opsOfChoice0 (R := Mom P.d → ℂ) j0 c (rootForm P σ nroot)]
    congr 1
    rw [Finset.prod_apply]
    push_cast
    refine Finset.prod_congr rfl fun t _ => ?_
    cases c t with
    | none => simp
    | some i =>
      simp only [Option.elim, Pi.pow_apply, rootForm, h0n]
      simp only [latticePoint, Int.cast_zero, zero_div]
      have h00 : (WithLp.toLp 2 (fun _ : Fin P.d => (0 : ℝ)) : Mom P.d) = 0 := by ext; simp
      rw [h00, add_zero]
      push_cast
      have : ((σ j0 : ℂ)) ^ 2 = 1 := by exact_mod_cast hσ2
      rw [mul_pow, this, one_mul]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← jbr_pow_expand x nn]

end WaveTurbulence.LGSpine
