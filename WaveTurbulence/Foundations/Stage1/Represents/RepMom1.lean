/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepOuterM
public import WaveTurbulence.Foundations.Stage1.Represents.RepSupM
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-D (moments): the modulation losses are paid by the slot moments

VINEEST(λ) costs `(1 + |λ_j|)^c` per unit (`c = 6η⁶`, R58).  The modulation `λ_j = modLam frq route j` is a sum of slot
frequencies routed to the unit `j`, and every slot clock is routed to at most one unit, so
`Π_j (1 + |λ_j|)^c ≤ Π_s Π_i (1 + |m_{s,i}|)^c` (`prod_modLam_le`), and `Π_i (1 + |m_i|)^c ≤ 9 ⟨m/2⟩^θ` for `2c ≤ θ`,
`c ≤ 1` (`prod_one_add_abs_le_maxBracketPow`): the moment `maxBracketPow θ (half m)` carried by the slot superpositions
(`SupM`, `CenSupM`) pays it.  `ennreal_tsum_pi_prod_fintype`: the sum over the modes of all slots of a product is the
product of the sums.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS Finset TTree Reg
  Reg.Skeleton WaveTurbulence.LGSpine
open scoped ENNReal

theorem one_add_abs_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    1 + |∑ i ∈ s, x i| ≤ ∏ i ∈ s, (1 + |x i|) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : 1 + |x a + ∑ i ∈ s, x i| ≤ (1 + |x a|) * (1 + |∑ i ∈ s, x i|) := by
      have := abs_add_le (x a) (∑ i ∈ s, x i)
      nlinarith [abs_nonneg (x a), abs_nonneg (∑ i ∈ s, x i)]
    exact h1.trans (mul_le_mul_of_nonneg_left ih (by positivity))

theorem one_add_abs_sum_rpow_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (1 + |∑ i ∈ s, x i|) ^ c ≤ ∏ i ∈ s, (1 + |x i|) ^ c := by
  rw [Real.finsetProd_rpow s _ (fun i _ => by positivity)]
  exact Real.rpow_le_rpow (by positivity) (one_add_abs_sum_le s x) hc

theorem one_le_one_add_abs_rpow (x : ℝ) {c : ℝ} (hc : 0 ≤ c) : 1 ≤ (1 + |x|) ^ c :=
  Real.one_le_rpow (by linarith [abs_nonneg x]) hc

/-- The unit losses are bounded by the losses of the routed slot frequencies. -/
theorem prod_modLam_le {w : ℕ} {G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    (frq : ReplacementSlot G → Fin 2 → ℤ) (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) {c : ℝ} (hc : 0 ≤ c) :
    ∏ j, (1 + |((modLam frq route j : ℤ) : ℝ)|) ^ c ≤ ∏ s, ∏ i, (1 + |(frq s i : ℝ)|) ^ c := by
  classical
  set y : ReplacementSlot G → Fin 2 → J → ℝ := fun s i j => if route s i = Sum.inr j then (frq s i : ℝ) else 0
    with hy
  have h1 : ∀ j, (1 + |((modLam frq route j : ℤ) : ℝ)|) ^ c ≤ ∏ s, ∏ i, (1 + |y s i j|) ^ c := by
    intro j
    have e : ((modLam frq route j : ℤ) : ℝ) = ∑ s, ∑ i, y s i j := by
      unfold modLam; push_cast; simp only [hy]
    rw [e]
    refine (one_add_abs_sum_rpow_le _ _ hc).trans (Finset.prod_le_prod₀ (fun s _ => by positivity) fun s _ => ?_)
    exact one_add_abs_sum_rpow_le _ _ hc
  refine (Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => h1 j).trans ?_
  rw [Finset.prod_comm]
  refine Finset.prod_le_prod₀ (fun s _ => by positivity) fun s _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
  rcases hr : route s i with yy | j0
  · have : ∀ j, (1 + |y s i j|) ^ c = 1 := fun j => by simp [hy, hr]
    simp only [this, Finset.prod_const_one]
    exact one_le_one_add_abs_rpow _ hc
  · have : ∀ j, (1 + |y s i j|) ^ c = if j0 = j then (1 + |(frq s i : ℝ)|) ^ c else 1 := by
      intro j
      by_cases hj : j0 = j
      · subst hj; simp [hy, hr]
      · have hne : route s i ≠ Sum.inr j := by rw [hr]; exact fun h => hj (Sum.inr_injective h)
        simp [hy, hne, hj]
    simp only [this, Finset.prod_ite_eq, Finset.mem_univ, ite_true, le_refl]

theorem one_add_abs_int_le (m : ℤ) : 1 + |(m : ℝ)| ≤ 3 * Real.sqrt (1 + ((m : ℝ) / 2) ^ 2) := by
  have h : (1 + |(m : ℝ)|) / 3 ≤ Real.sqrt (1 + ((m : ℝ) / 2) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    have ha := abs_nonneg (m : ℝ)
    have hs : |(m : ℝ)| ^ 2 = (m : ℝ) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|(m : ℝ)| - 1)]
  linarith

/-- Two clock frequencies with loss exponent `c` are paid by the slot moment `θ ≥ 2c` (`c ≤ 1`). -/
theorem prod_one_add_abs_le_maxBracketPow (m : Fin 2 → ℤ) {c θ : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcθ : 2 * c ≤ θ) :
    ENNReal.ofReal (∏ i, (1 + |(m i : ℝ)|) ^ c) ≤ 9 * maxBracketPow θ (half m) := by
  unfold maxBracketPow half
  set X : ℝ := (⨆ i, Real.sqrt (1 + ((m i : ℝ) / 2) ^ 2)) ⊔ 1 with hX
  have hX1 : 1 ≤ X := le_sup_right
  have hbdd : BddAbove (Set.range fun i : Fin 2 => Real.sqrt (1 + ((m i : ℝ) / 2) ^ 2)) := (Set.finite_range _).bddAbove
  have hi : ∀ i, 1 + |(m i : ℝ)| ≤ 3 * X := fun i =>
    (one_add_abs_int_le (m i)).trans (mul_le_mul_of_nonneg_left
      ((le_ciSup hbdd i).trans le_sup_left) (by norm_num))
  have h1 : ∏ i, (1 + |(m i : ℝ)|) ^ c ≤ ∏ _i : Fin 2, (3 * X) ^ c :=
    Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => Real.rpow_le_rpow (by positivity) (hi i) hc
  have h2 : ∏ _i : Fin 2, (3 * X) ^ c = (3 : ℝ) ^ (2 * c) * X ^ (2 * c) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.mul_rpow (by norm_num) (by linarith),
      mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by linarith)]
    ring_nf
  have h3 : (3 : ℝ) ^ (2 * c) ≤ 9 := by
    calc (3 : ℝ) ^ (2 * c) ≤ (3 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 9 := by norm_num
  have h4 : X ^ (2 * c) ≤ X ^ θ := Real.rpow_le_rpow_of_exponent_le hX1 hcθ
  have h5 : ∏ i, (1 + |(m i : ℝ)|) ^ c ≤ 9 * X ^ θ := by
    calc _ ≤ (3 : ℝ) ^ (2 * c) * X ^ (2 * c) := h1.trans (le_of_eq h2)
      _ ≤ 9 * X ^ θ := mul_le_mul h3 h4 (by positivity) (by norm_num)
  calc ENNReal.ofReal (∏ i, (1 + |(m i : ℝ)|) ^ c) ≤ ENNReal.ofReal (9 * X ^ θ) := ENNReal.ofReal_le_ofReal h5
    _ = 9 * ENNReal.ofReal (X ^ θ) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

/-- The sum over the modes of all slots of a product is the product of the per-slot sums. -/
theorem ennreal_tsum_pi_prod_fintype {ι : Type*} [Fintype ι] {M : ι → Type*} (f : ∀ i, M i → ℝ≥0∞) :
    ∑' m : ∀ i, M i, ∏ i, f i (m i) = ∏ i, ∑' m, f i m := by
  classical
  set e := Fintype.equivFin ι
  have h := ennreal_tsum_pi_prod_dep (Fintype.card ι) (M := fun k => M (e.symm k)) (fun k => f (e.symm k))
  have hl : ∑' m : ∀ i, M i, ∏ i, f i (m i) =
      ∑' m : ∀ k, M (e.symm k), ∏ k, f (e.symm k) (m k) := by
    rw [← (Equiv.piCongrLeft' M e).tsum_eq]
    refine tsum_congr fun m => ?_
    rw [← e.symm.prod_comp]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [Equiv.piCongrLeft'_apply]
  rw [hl, h]
  exact e.symm.prod_comp (fun i => ∑' m, f i m)

end WaveTurbulence.Represents
