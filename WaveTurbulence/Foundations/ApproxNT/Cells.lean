/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ApproxNT.Statement
public import WaveTurbulence.Foundations.ApproxNT.Cell

/-!
# Cells and the triangular structure (packet NT6)

A cell configuration `pq : Fin n → ℤ^d × ℤ^d` localizes `x_j` near `p_j` and `y_j` near `q_j` through
`cellWeight pq x y = ∏_j θ(x_j - p_j) θ(y_j - q_j)`; these weights form a partition of unity.

The triangular structure of DH23 (propertyw2) is used only to count the cells meeting the support
set `E`: such a cell satisfies `|p̃_j - a_j|_∞ ≤ λ_j + 2`, `|q̃_j - b_j|_∞ ≤ λ_j + 2`, and
`pq ↦ (p̃, q̃)` is injective (well-founded induction along `≺`). Hence at most
`∏_j (2λ_j + 5)^{2d}` cells meet `E`. (This replaces the source's localization at scale `λ_j`;
it needs no upper bound on `λ_j`.)
-/

public section

noncomputable section

open MeasureTheory Finset WithLp

namespace WaveTurbulence.ApproxNT

variable {d n : ℕ}

/-- The integer version of a shift. -/
@[expose] def Shift.evalZ : Shift n → (Fin n → Fin d → ℤ) → (Fin n → Fin d → ℤ) → (Fin d → ℤ)
  | .zero, _, _ => 0
  | .x j s, X, _ => if s then X j else -X j
  | .y j s, _, Y => if s then Y j else -Y j

theorem Shift.eval_intVec (σ : Shift n) (P Q : Fin n → Fin d → ℤ) :
    σ.eval (fun j => NTSP.intVec (P j)) (fun j => NTSP.intVec (Q j)) = NTSP.intVec (σ.evalZ P Q) := by
  cases σ with
  | zero => simp [Shift.eval, Shift.evalZ, NTSP.intVec_zero]
  | x j s => cases s <;> ext i <;> simp [Shift.eval, Shift.evalZ, NTSP.intVec]
  | y j s => cases s <;> ext i <;> simp [Shift.eval, Shift.evalZ, NTSP.intVec]

theorem Shift.eval_sub (σ : Shift n) (X Y X' Y' : Fin n → Mom d) :
    σ.eval X Y - σ.eval X' Y' = σ.eval (X - X') (Y - Y') := by
  cases σ with
  | zero => simp [Shift.eval]
  | x j s =>
    cases s
    · simp only [Shift.eval, Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]; abel
    · simp [Shift.eval]
  | y j s =>
    cases s
    · simp only [Shift.eval, Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]; abel
    · simp [Shift.eval]

theorem Shift.evalZ_congr {lt : Fin n → Fin n → Prop} {k : Fin n} {σ : Shift n} (hσ : σ.Below lt k)
    {P Q P' Q' : Fin n → Fin d → ℤ} (h : ∀ j, lt j k → P j = P' j ∧ Q j = Q' j) :
    σ.evalZ P Q = σ.evalZ P' Q' := by
  cases σ with
  | zero => rfl
  | x j s => simp only [Shift.evalZ, (h j hσ).1]
  | y j s => simp only [Shift.evalZ, (h j hσ).2]

/-- The weight of a cell configuration. -/
@[expose] def cellWeight (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) (x y : Fin n → Mom d) : ℂ :=
  ∏ j, cellAmp (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (x j) (y j)

/-- The cells that can be active at `(x, y)`. -/
@[expose] def localCells (x y : Fin n → Mom d) : Finset (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :=
  Fintype.piFinset fun j => thetaSupport (x j) ×ˢ thetaSupport (y j)

theorem cellWeight_eq_zero {pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)} {x y : Fin n → Mom d}
    (h : pq ∉ localCells x y) : cellWeight pq x y = 0 := by
  rw [localCells, Fintype.mem_piFinset] at h
  simp only [not_forall] at h
  obtain ⟨j, hj⟩ := h
  refine prod_eq_zero (mem_univ j) ?_
  rw [mem_product, not_and_or] at hj
  rcases hj with h1 | h1
  · simp [cellAmp, thetaC, thetaMom_sub_eq_zero h1]
  · simp [cellAmp, thetaC, thetaMom_sub_eq_zero h1]

/-- The cell weights form a partition of unity. -/
theorem sum_cellWeight (x y : Fin n → Mom d) :
    ∑ pq ∈ localCells x y, cellWeight pq x y = 1 := by
  simp only [localCells, cellWeight]
  rw [← prod_univ_sum (fun j => thetaSupport (x j) ×ˢ thetaSupport (y j))
    (fun j (g : (Fin d → ℤ) × (Fin d → ℤ)) =>
      cellAmp (NTSP.intVec g.1) (NTSP.intVec g.2) (x j) (y j))]
  refine prod_eq_one fun j _ => ?_
  rw [sum_product]
  simp only [cellAmp, thetaC]
  simp_rw [← mul_sum, ← sum_mul]
  have h1 := sum_thetaMom (x j)
  have h2 := sum_thetaMom (y j)
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, h1, h2]
  simp

/-- The tilde of a cell configuration, `(p̃_j, q̃_j)`. -/
@[expose] def cellTilde (xs ys : Fin n → Shift n) (pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :
    Fin n → (Fin d → ℤ) × (Fin d → ℤ) :=
  fun j => ((pq j).1 + (xs j).evalZ (fun i => (pq i).1) (fun i => (pq i).2),
    (pq j).2 + (ys j).evalZ (fun i => (pq i).1) (fun i => (pq i).2))

/-- The tilde map is injective (well-founded induction along `≺`). -/
theorem cellTilde_injective {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j) :
    Function.Injective (cellTilde (d := d) xs ys) := by
  intro pq pq' h
  have hwf : WellFounded lt := Finite.wellFounded_of_trans_of_irrefl lt
  funext j
  induction j using hwf.induction with
  | _ j ih =>
    have hj := congrFun h j
    simp only [cellTilde, Prod.mk.injEq] at hj
    have hb : ∀ i, lt i j → (pq i).1 = (pq' i).1 ∧ (pq i).2 = (pq' i).2 := fun i hi => by
      rw [ih i hi]; exact ⟨rfl, rfl⟩
    rw [Shift.evalZ_congr (hxs j) (P' := fun i => (pq' i).1) (Q' := fun i => (pq' i).2) hb] at hj
    rw [Shift.evalZ_congr (hys j) (P' := fun i => (pq' i).1) (Q' := fun i => (pq' i).2) hb] at hj
    exact Prod.ext (add_right_cancel hj.1) (add_right_cancel hj.2)

/-- The integer box `|z - a|_∞ ≤ R`. -/
@[expose] def intBox (a : Mom d) (R : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Icc ⌈a i - R⌉ ⌊a i + R⌋

theorem mem_intBox {a : Mom d} {R : ℝ} {z : Fin d → ℤ} (h : ∀ i, |(z i : ℝ) - a i| ≤ R) :
    z ∈ intBox a R := by
  rw [intBox, Fintype.mem_piFinset]
  intro i
  have := abs_le.mp (h i)
  rw [mem_Icc]
  exact ⟨Int.ceil_le.2 (by linarith), Int.le_floor.2 (by linarith)⟩

theorem card_intBox_le (a : Mom d) {R : ℝ} (hR : 0 ≤ R) :
    ((intBox a R).card : ℝ) ≤ (2 * R + 1) ^ d := by
  rw [intBox, Fintype.card_piFinset]
  push_cast
  calc ∏ i, ((Icc ⌈a i - R⌉ ⌊a i + R⌋).card : ℝ) ≤ ∏ _i : Fin d, (2 * R + 1) := by
        refine prod_le_prod₀ (fun _ _ => by positivity) fun i _ => ?_
        rw [Int.card_Icc]
        have h1 := Int.le_ceil (a i - R)
        have h2 := Int.floor_le (a i + R)
        rcases le_or_gt (⌊a i + R⌋ + 1 - ⌈a i - R⌉) 0 with h | h
        · rw [Int.toNat_of_nonpos h]; push_cast; linarith
        · rw [show (((⌊a i + R⌋ + 1 - ⌈a i - R⌉).toNat : ℕ) : ℝ) =
              ((⌊a i + R⌋ + 1 - ⌈a i - R⌉ : ℤ) : ℝ) by
            rw [← Int.cast_natCast, Int.toNat_of_nonneg h.le]]
          push_cast; linarith
    _ = (2 * R + 1) ^ d := by simp

/-- The cells meeting the support set, described through the tilde box. -/
@[expose] def cellBox (xs ys : Fin n → Shift n) (a b : Fin n → Mom d) (lam : Fin n → ℝ) :
    Set (Fin n → (Fin d → ℤ) × (Fin d → ℤ)) :=
  {pq | cellTilde xs ys pq ∈ Fintype.piFinset fun j => intBox (a j) (lam j + 2) ×ˢ intBox (b j) (lam j + 2)}

theorem cellBox_finite {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    (a b : Fin n → Mom d) (lam : Fin n → ℝ) : (cellBox xs ys a b lam).Finite :=
  Set.Finite.of_finite_image (Set.Finite.subset (Fintype.piFinset _).finite_toSet
    (fun z ⟨pq, hpq, h⟩ => by rw [← h]; exact hpq)) (cellTilde_injective hxs hys).injOn

/-- At most `∏_j (2λ_j + 5)^{2d}` cells meet the support set. -/
theorem card_cellBox_le {lt : Fin n → Fin n → Prop} [IsStrictOrder (Fin n) lt]
    {xs ys : Fin n → Shift n} (hxs : ∀ j, (xs j).Below lt j) (hys : ∀ j, (ys j).Below lt j)
    (a b : Fin n → Mom d) {lam : Fin n → ℝ} (hlam : ∀ j, 0 ≤ lam j) :
    ((cellBox_finite hxs hys a b lam).toFinset.card : ℝ) ≤ ∏ j, (2 * lam j + 5) ^ (2 * d) := by
  set B := Fintype.piFinset fun j => intBox (a j) (lam j + 2) ×ˢ intBox (b j) (lam j + 2)
  have hcard : (cellBox_finite hxs hys a b lam).toFinset.card ≤ B.card := by
    refine card_le_card_of_injOn (cellTilde xs ys) (fun pq hpq => ?_)
      ((cellTilde_injective hxs hys).injOn)
    have h1 : pq ∈ cellBox xs ys a b lam :=
      (Set.Finite.mem_toFinset (cellBox_finite hxs hys a b lam)).1 (Finset.mem_coe.1 hpq)
    exact h1
  calc ((cellBox_finite hxs hys a b lam).toFinset.card : ℝ) ≤ B.card := by exact_mod_cast hcard
    _ = ∏ j, ((intBox (a j) (lam j + 2)).card * (intBox (b j) (lam j + 2)).card : ℝ) := by
        simp [B, Fintype.card_piFinset, card_product]
    _ ≤ ∏ j, (2 * lam j + 5) ^ (2 * d) := by
        refine prod_le_prod₀ (fun _ _ => by positivity) fun j _ => ?_
        have h1 := card_intBox_le (a j) (by linarith [hlam j] : 0 ≤ lam j + 2)
        have h2 := card_intBox_le (b j) (by linarith [hlam j] : 0 ≤ lam j + 2)
        rw [pow_mul, sq, mul_pow]
        calc ((intBox (a j) (lam j + 2)).card * (intBox (b j) (lam j + 2)).card : ℝ)
            ≤ (2 * (lam j + 2) + 1) ^ d * (2 * (lam j + 2) + 1) ^ d :=
              mul_le_mul h1 h2 (by positivity) (by have := hlam j; positivity)
          _ = _ := by ring_nf

theorem abs_coord_le_norm (v : Mom d) (i : Fin d) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  simpa [Real.norm_eq_abs] using this

/-- An active cell at a point of the support set lies in the cell box. -/
theorem mem_cellBox {xs ys : Fin n → Shift n} {a b : Fin n → Mom d} {lam : Fin n → ℝ}
    {pq : Fin n → (Fin d → ℤ) × (Fin d → ℤ)} {x y : Fin n → Mom d}
    (hE : (x, y) ∈ supportSet xs ys a b lam) (hw : cellWeight pq x y ≠ 0) :
    pq ∈ cellBox xs ys a b lam := by
  have hθ : ∀ j, (∀ i, |(x j - NTSP.intVec (pq j).1) i| < 1) ∧
      (∀ i, |(y j - NTSP.intVec (pq j).2) i| < 1) := by
    intro j
    have hj : cellAmp (NTSP.intVec (pq j).1) (NTSP.intVec (pq j).2) (x j) (y j) ≠ 0 :=
      fun h => hw (prod_eq_zero (mem_univ j) h)
    have h1 : thetaMom d (x j - NTSP.intVec (pq j).1) ≠ 0 := by
      intro h; apply hj; simp [cellAmp, thetaC, h]
    have h2 : thetaMom d (y j - NTSP.intVec (pq j).2) ≠ 0 := by
      intro h; apply hj; simp [cellAmp, thetaC, h]
    exact ⟨abs_lt_one_of_thetaMom_ne_zero h1, abs_lt_one_of_thetaMom_ne_zero h2⟩
  have hθ1 : ∀ j i, |x j i - (NTSP.intVec (pq j).1) i| < 1 := fun j i => by
    simpa using (hθ j).1 i
  have hθ2 : ∀ j i, |y j i - (NTSP.intVec (pq j).2) i| < 1 := fun j i => by
    simpa using (hθ j).2 i
  have hsh : ∀ (σ : Shift n) (i : Fin d),
      |(σ.eval x y - σ.eval (fun j => NTSP.intVec (pq j).1) (fun j => NTSP.intVec (pq j).2)) i| ≤ 1 := by
    intro σ i
    rw [Shift.eval_sub]
    cases σ with
    | zero => simp [Shift.eval]
    | x j s =>
      have := abs_lt.mp (hθ1 j i)
      cases s <;> simp only [Shift.eval, Bool.false_eq_true, ↓reduceIte, Pi.sub_apply,
        PiLp.neg_apply, PiLp.sub_apply] <;> rw [abs_le] <;> constructor <;> linarith
    | y j s =>
      have := abs_lt.mp (hθ2 j i)
      cases s <;> simp only [Shift.eval, Bool.false_eq_true, ↓reduceIte, Pi.sub_apply,
        PiLp.neg_apply, PiLp.sub_apply] <;> rw [abs_le] <;> constructor <;> linarith
  rw [cellBox, Set.mem_ofPred_eq, Fintype.mem_piFinset]
  intro j
  rw [mem_product]
  obtain ⟨hEx, hEy⟩ := hE j
  constructor
  · refine mem_intBox fun i => ?_
    have e1 := abs_coord_le_norm (x j + (xs j).eval x y - a j) i
    have e2 := hsh (xs j) i
    have e3 := (hθ j).1 i
    simp only [cellTilde, Pi.add_apply, Int.cast_add]
    rw [← NTSP.intVec_apply, ← NTSP.intVec_apply, ← Shift.eval_intVec]
    simp only [PiLp.add_apply, PiLp.sub_apply] at e1 e2 e3
    rw [abs_le] at *
    rw [abs_lt] at e3
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
  · refine mem_intBox fun i => ?_
    have e1 := abs_coord_le_norm (y j + (ys j).eval x y - b j) i
    have e2 := hsh (ys j) i
    have e3 := (hθ j).2 i
    simp only [cellTilde, Pi.add_apply, Int.cast_add]
    rw [← NTSP.intVec_apply, ← NTSP.intVec_apply, ← Shift.eval_intVec]
    simp only [PiLp.add_apply, PiLp.sub_apply] at e1 e2 e3
    rw [abs_le] at *
    rw [abs_lt] at e3
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

end WaveTurbulence.ApproxNT
