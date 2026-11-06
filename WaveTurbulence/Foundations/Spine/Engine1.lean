/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.AmpExpansion
public import WaveTurbulence.Foundations.Spine.DecoupleFin
/-! # Factorization engine, algebra (S3b LADDER-DECAY)

Pointwise algebra: for fixed modulation `ξ` and time `t`, the constrained rung sum with the
modulation phases is bounded by an average over finite characters of products of one-rung sums
with an additive linear phase. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset MeasureTheory WaveTurbulence WaveTurbulence.WeylSums
open scoped FourierTransform

variable {d n : ℕ}

/-- A rung point: the pair `(x, y)` of integer difference vectors. -/
abbrev Pt (d : ℕ) := (Fin d → ℤ) × (Fin d → ℤ)

lemma latticePoint_add' (L : ℝ) (m k : Fin d → ℤ) :
    latticePoint L (m + k) = latticePoint L m + latticePoint L k := by
  ext j; simp [latticePoint, add_div]

lemma latticePoint_zero' (L : ℝ) : latticePoint L (0 : Fin d → ℤ) = 0 := by
  ext j; simp [latticePoint]

lemma fourierChar_eq_e (x : ℝ) : (Real.fourierChar x : ℂ) = e x := by
  rw [Real.fourierChar_apply, e]

/-- Affine integer labels `c + ∑_k λ_k (P_k)`. -/
structure AffLab (d n : ℕ) where
  c : Fin d → ℤ
  lam : Fin n → (Pt d →+ (Fin d → ℤ))

/-- Value of an affine label on a rung configuration. -/
def AffLab.eval (A : AffLab d n) (P : Fin n → Pt d) : Fin d → ℤ := A.c + ∑ k, A.lam k (P k)

variable {ι : Type*} [Fintype ι]

/-- The additive phase seen by rung `k` from modulation `ξ`. -/
noncomputable def nuK (L : ℝ) (lab : ι → AffLab d n) (ξ : ι → Mom d) (k : Fin n) : Pt d →+ ℝ where
  toFun p := ∑ b, inner ℝ (ξ b) (latticePoint L ((lab b).lam k p))
  map_zero' := by simp [latticePoint_zero']
  map_add' p q := by
    simp only [map_add, latticePoint_add', inner_add_right, Finset.sum_add_distrib]

/-- The constant (unimodular) phase of the modulation. -/
noncomputable def cst (L : ℝ) (base : Mom d) (lab : ι → AffLab d n) (ξ : ι → Mom d) : ℝ :=
  ∑ b, inner ℝ (ξ b) (base + latticePoint L (lab b).c)

lemma sum_inner_eval (L : ℝ) (base : Mom d) (lab : ι → AffLab d n) (ξ : ι → Mom d)
    (P : Fin n → Pt d) :
    ∑ b, inner ℝ (ξ b) (base + latticePoint L ((lab b).eval P)) =
      cst L base lab ξ + ∑ k, nuK L lab ξ k (P k) := by
  have h : ∀ b, latticePoint L ((lab b).eval P) =
      latticePoint L (lab b).c + ∑ k, latticePoint L ((lab b).lam k (P k)) := by
    intro b
    rw [AffLab.eval, latticePoint_add']
    congr 1
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp [latticePoint_zero']
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, latticePoint_add', ih]
  simp_rw [h]
  simp only [cst, nuK, AddMonoidHom.coe_mk, ZeroHom.coe_mk, inner_add_right, inner_sum,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  ring

/-- The character `p ↦ ∑_i j_i Δ(p)_i / M`. -/
noncomputable def psiK (M : ℕ) (Δ : Pt d →+ (Fin d → ℤ)) (j : Fin d → Fin M) : Pt d →+ ℝ where
  toFun p := ∑ i, ((j i : ℕ) : ℝ) * (Δ p i : ℝ) / M
  map_zero' := by simp
  map_add' p q := by
    simp only [map_add, Pi.add_apply, Int.cast_add, mul_add, add_div, Finset.sum_add_distrib]

/-- A modulus exceeding every constraint defect. -/
lemma exists_modulus {S : Fin n → Finset (Pt d)} (Δ : Fin n → (Pt d →+ (Fin d → ℤ)))
    (c0 : Fin d → ℤ) :
    ∃ M : ℕ, 0 < M ∧ ∀ P ∈ Fintype.piFinset S, ∀ i, |(∑ k, Δ k (P k)) i - c0 i| < M := by
  refine ⟨(∑ k, ∑ p ∈ S k, ∑ i, (Δ k p i).natAbs + ∑ i, (c0 i).natAbs) + 1, Nat.succ_pos _, ?_⟩
  intro P hP i
  rw [Fintype.mem_piFinset] at hP
  have h1 : |(∑ k, Δ k (P k)) i| ≤ ∑ k, ∑ p ∈ S k, ∑ i', |Δ k p i'| := by
    rw [Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
    refine le_trans ?_ (Finset.single_le_sum (f := fun p => ∑ i', |Δ k p i'|)
      (fun p _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (hP k))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i' => |Δ k (P k) i'|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    exact le_rfl
  have h2 : |c0 i| ≤ ∑ i', |c0 i'| :=
    Finset.single_le_sum (f := fun i' => |c0 i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h3 := abs_sub (((∑ k, Δ k (P k)) i)) (c0 i)
  push_cast
  linarith


/-- **Pointwise decoupled bound.** For fixed modulation and fixed times, the constrained sum is
dominated by an average over finite characters of products of one-rung twisted sums. -/
theorem constrained_phase_sum_norm_le [DecidableEq ι] {S : Fin n → Finset (Pt d)}
    (L : ℝ) (base : Mom d) (lab : ι → AffLab d n) (ξ : ι → Mom d)
    (Wt : Fin n → Pt d → ℂ) (Δ : Fin n → (Pt d →+ (Fin d → ℤ))) (c0 : Fin d → ℤ)
    (M : ℕ) (hM : 0 < M)
    (hb : ∀ P ∈ Fintype.piFinset S, ∀ i, |(∑ k, Δ k (P k)) i - c0 i| < M) :
    ‖∑ P ∈ Fintype.piFinset S, (if ∑ k, Δ k (P k) = c0 then
        (∏ b, e (inner ℝ (ξ b) (base + latticePoint L ((lab b).eval P)))) *
          ∏ k, Wt k (P k) else 0)‖ ≤
      ((M : ℝ) ^ d)⁻¹ * ∑ j : Fin d → Fin M,
        ∏ k, ‖∑ p ∈ S k, Wt k p * e ((nuK L lab ξ k + psiK M (Δ k) j) p)‖ := by
  have h1 : ∀ P : Fin n → Pt d, (∏ b, e (inner ℝ (ξ b) (base + latticePoint L ((lab b).eval P)))) =
      e (cst L base lab ξ) * ∏ k, e (nuK L lab ξ k (P k)) := by
    intro P
    rw [← e_sum, sum_inner_eval, e_add, e_sum]
  have h2 : (∑ P ∈ Fintype.piFinset S, (if ∑ k, Δ k (P k) = c0 then
        (∏ b, e (inner ℝ (ξ b) (base + latticePoint L ((lab b).eval P)))) *
          ∏ k, Wt k (P k) else 0)) =
      e (cst L base lab ξ) * ∑ P ∈ Fintype.piFinset S, (if ∑ k, Δ k (P k) = c0 then
        ∏ k, (Wt k (P k) * e (nuK L lab ξ k (P k))) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    split_ifs
    · rw [h1, Finset.prod_mul_distrib]; ring
    · simp
  classical
  rw [h2, norm_mul, norm_e, one_mul,
    constrained_sum_eq_avg S (fun k p => Wt k p * e (nuK L lab ξ k p)) (fun k p => Δ k p) c0 M hM hb]
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  rw [norm_mul, norm_e, one_mul, norm_prod]
  refine le_of_eq (Finset.prod_congr rfl (fun k _ => ?_))
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  simp only [AddMonoidHom.add_apply, psiK, AddMonoidHom.coe_mk, ZeroHom.coe_mk, e_add]
  ring

end WaveTurbulence.LadderDecay
