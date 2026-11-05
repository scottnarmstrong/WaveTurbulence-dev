/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
/-! # Interior chain algebra of a ladder (S3b LADDER-DECAY)

Pure algebra of the interior rungs of a ladder: slot signs, anchor parametrization of the
four labels at an atom by two difference variables, and the rail recursion. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset

variable {n : ℕ} {E : Type*} [AddCommGroup E]

/-- Anchor offsets `(0, x+y, x, y)` of the four labels at an atom (two plus, two minus slots). -/
def tvec (x y : E) : Fin 4 → E := ![0, x + y, x, y]

/-- Sign pattern at the interior rungs: slots 0,1 are rung darts, 2 the dart toward the lower
neighbour, 3 the dart toward the upper neighbour; `σ i` sorts them into plus,plus,minus,minus. -/
structure ChainSigns (n : ℕ) where
  sg : Fin n → Fin 4 → ℤ
  σ : Fin n → Equiv.Perm (Fin 4)
  plus : ∀ i, sg i (σ i 0) = 1 ∧ sg i (σ i 1) = 1
  minus : ∀ i, sg i (σ i 2) = -1 ∧ sg i (σ i 3) = -1
  link : ∀ i j : Fin n, i.1 + 1 = j.1 → sg j 2 = - sg i 3

/-- Labels of the interior bonds: rung bonds, u-rails `a`, v-rails `b` (rail `i` joins rung
`i-1` and rung `i`; interior rung `i` has in-rail `i` and out-rail `i+1`). -/
@[ext] structure ChainLab (n : ℕ) (E : Type*) where
  r : Fin n → Fin 2 → E
  a : Fin (n + 1) → E
  b : Fin (n + 1) → E

namespace ChainLab
variable (L : ChainLab n E)
def uSlot (i : Fin n) : Fin 4 → E := ![L.r i 0, L.r i 1, L.a i.castSucc, L.a i.succ]
def vSlot (i : Fin n) : Fin 4 → E := ![L.r i 0, L.r i 1, L.b i.castSucc, L.b i.succ]
end ChainLab

def ChainSigns.IsSol (S : ChainSigns n) (L : ChainLab n E) : Prop :=
  ∀ i : Fin n, (∑ k, S.sg i k • L.uSlot i k = 0) ∧ (∑ k, S.sg i k • L.vSlot i k = 0)

namespace ChainSigns
variable (S : ChainSigns n)

lemma sum_perm (i : Fin n) (lab : Fin 4 → E) :
    ∑ k, S.sg i k • lab k = lab (S.σ i 0) + lab (S.σ i 1) - lab (S.σ i 2) - lab (S.σ i 3) := by
  rw [← Equiv.sum_comp (S.σ i)]
  rw [Fin.sum_univ_four]
  obtain ⟨h0, h1⟩ := S.plus i
  obtain ⟨h2, h3⟩ := S.minus i
  rw [h0, h1, h2, h3]
  simp only [one_smul, neg_smul]
  abel

lemma slot_eq (i : Fin n) (lab : Fin 4 → E) (h : ∑ k, S.sg i k • lab k = 0) (s : Fin 4) :
    lab s = lab (S.σ i 0) -
      tvec (lab (S.σ i 0) - lab (S.σ i 2)) (lab (S.σ i 0) - lab (S.σ i 3)) ((S.σ i).symm s) := by
  rw [S.sum_perm i lab] at h
  have key : lab (S.σ i 1) = lab (S.σ i 2) + lab (S.σ i 3) - lab (S.σ i 0) := by
    rw [← sub_eq_zero, ← h]; abel
  obtain ⟨k, rfl⟩ := (S.σ i).surjective s
  rw [Equiv.symm_apply_apply]
  fin_cases k <;> simp [tvec]
  · rw [key]; abel


lemma sg_pm (i : Fin n) (k : Fin 4) : S.sg i k = 1 ∨ S.sg i k = -1 := by
  obtain ⟨k', rfl⟩ := (S.σ i).surjective k
  obtain ⟨h0, h1⟩ := S.plus i
  obtain ⟨h2, h3⟩ := S.minus i
  fin_cases k'
  · exact Or.inl h0
  · exact Or.inl h1
  · exact Or.inr h2
  · exact Or.inr h3

lemma sg_sq (i : Fin n) (k : Fin 4) : S.sg i k * S.sg i k = 1 := by
  rcases S.sg_pm i k with h | h <;> rw [h] <;> norm_num

/-- Offsets of the four slots in the anchor parametrization. -/
def tau (P : Fin n → E × E) (i : Fin n) (s : Fin 4) : E :=
  tvec (P i).1 (P i).2 ((S.σ i).symm s)

/-- The u-rail labels reconstructed from the first rail and the pairs. -/
def railU (a0 : E) (P : Fin n → E × E) (j : Fin (n + 1)) : E :=
  a0 + ∑ k : Fin n, if k.1 < j.1 then (S.tau P k 2 - S.tau P k 3) else 0

/-- Sign factor relating the rail gaps `a_j - b_j = eps_j • (a_0 - b_0)`. -/
def epsF (j : Fin (n + 1)) : ℤ :=
  ∏ k : Fin n, if k.1 < j.1 then -(S.sg k 3 * S.sg k 2) else 1

lemma railU_zero (a0 : E) (P : Fin n → E × E) : S.railU a0 P 0 = a0 := by
  simp [railU]

lemma epsF_zero : S.epsF 0 = 1 := by
  simp [epsF]


end ChainSigns

lemma sum_lt_succ (f : Fin n → E) (j : Fin n) :
    (∑ k : Fin n, if k.1 < j.1 + 1 then f k else 0) =
      (∑ k : Fin n, if k.1 < j.1 then f k else 0) + f j := by
  have h : ∀ k : Fin n, (if k.1 < j.1 + 1 then f k else 0) =
      (if k.1 < j.1 then f k else 0) + (if k = j then f k else 0) := by
    intro k
    by_cases h1 : k.1 < j.1
    · have : k ≠ j := fun h => by subst h; omega
      simp [h1, this]; omega
    · by_cases h2 : k = j
      · subst h2; simp
      · have : ¬ k.1 < j.1 + 1 := by
          intro h3
          apply h2
          apply Fin.ext
          omega
        simp [h1, h2, this]
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  congr 1
  simp

lemma prod_lt_succ (f : Fin n → ℤ) (j : Fin n) :
    (∏ k : Fin n, if k.1 < j.1 + 1 then f k else 1) =
      (∏ k : Fin n, if k.1 < j.1 then f k else 1) * f j := by
  have h : ∀ k : Fin n, (if k.1 < j.1 + 1 then f k else 1) =
      (if k.1 < j.1 then f k else 1) * (if k = j then f k else 1) := by
    intro k
    by_cases h1 : k.1 < j.1
    · have : k ≠ j := fun h => by subst h; omega
      simp [h1, this]; omega
    · by_cases h2 : k = j
      · subst h2; simp
      · have : ¬ k.1 < j.1 + 1 := by
          intro h3
          apply h2
          apply Fin.ext
          omega
        simp [h1, h2, this]
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp

namespace ChainSigns
variable (S : ChainSigns n)

lemma railU_succ (a0 : E) (P : Fin n → E × E) (j : Fin n) :
    S.railU a0 P j.succ = S.railU a0 P j.castSucc + (S.tau P j 2 - S.tau P j 3) := by
  unfold railU
  rw [add_assoc]
  congr 1
  exact sum_lt_succ (fun k => S.tau P k 2 - S.tau P k 3) j

lemma epsF_succ (j : Fin n) :
    S.epsF j.succ = S.epsF j.castSucc * (-(S.sg j 3 * S.sg j 2)) := by
  unfold epsF
  exact prod_lt_succ (fun k => -(S.sg k 3 * S.sg k 2)) j


/-- Slot embedding of the two rung darts. -/
def rungSlot (k : Fin 2) : Fin 4 := Fin.castLE (by norm_num) k

/-- The ladder labels reconstructed from the chart `(a_0, b_0, pairs)`. -/
def inv (a0 b0 : E) (P : Fin n → E × E) : ChainLab n E where
  r i k := S.railU a0 P i.castSucc + S.tau P i 2 - S.tau P i (rungSlot k)
  a := S.railU a0 P
  b j := S.railU a0 P j - S.epsF j • (a0 - b0)

lemma inv_uSlot (a0 b0 : E) (P : Fin n → E × E) (i : Fin n) (s : Fin 4) :
    (S.inv a0 b0 P).uSlot i s = S.railU a0 P i.castSucc + S.tau P i 2 - S.tau P i s := by
  fin_cases s
  · simp [ChainLab.uSlot, inv, rungSlot]
  · simp [ChainLab.uSlot, inv, rungSlot]
  · simp [ChainLab.uSlot, inv]
  · simp [ChainLab.uSlot, inv, railU_succ]; abel

lemma tau_perm (P : Fin n → E × E) (i : Fin n) (k : Fin 4) :
    S.tau P i (S.σ i k) = tvec (P i).1 (P i).2 k := by
  simp [tau]

lemma isSol_inv (a0 b0 : E) (P : Fin n → E × E) : S.IsSol (S.inv a0 b0 P) := by
  intro i
  have hu : ∑ k, S.sg i k • (S.inv a0 b0 P).uSlot i k = 0 := by
    rw [S.sum_perm i, S.inv_uSlot, S.inv_uSlot, S.inv_uSlot, S.inv_uSlot]
    simp only [tau_perm]
    simp [tvec]
    abel
  refine ⟨hu, ?_⟩
  have h1 : ∑ k, S.sg i k • (S.inv a0 b0 P).vSlot i k =
      ∑ k, S.sg i k • (S.inv a0 b0 P).uSlot i k +
        (S.sg i 2 • ((S.inv a0 b0 P).b i.castSucc - (S.inv a0 b0 P).a i.castSucc) +
         S.sg i 3 • ((S.inv a0 b0 P).b i.succ - (S.inv a0 b0 P).a i.succ)) := by
    simp only [Fin.sum_univ_four, ChainLab.uSlot, ChainLab.vSlot]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, smul_sub]
    abel
  rw [h1, hu, zero_add]
  have hb : ∀ j : Fin (n + 1), (S.inv a0 b0 P).b j - (S.inv a0 b0 P).a j = -(S.epsF j • (a0 - b0)) := by
    intro j; simp [inv]
  rw [hb, hb, epsF_succ]
  have hsq := S.sg_sq i 3
  simp only [smul_neg, ← neg_add, neg_eq_zero]
  rw [← mul_smul, ← mul_smul]
  have : S.sg i 2 * S.epsF i.castSucc + S.sg i 3 * (S.epsF i.castSucc * -(S.sg i 3 * S.sg i 2)) = 0 := by
    linear_combination (-(S.epsF i.castSucc * S.sg i 2)) * hsq
  rw [← add_smul, this, zero_smul]

/-- The chart coordinates of a ladder labelling. -/
def pairs (L : ChainLab n E) (i : Fin n) : E × E :=
  (L.uSlot i (S.σ i 0) - L.uSlot i (S.σ i 2), L.uSlot i (S.σ i 0) - L.uSlot i (S.σ i 3))

lemma uSlot_eq (L : ChainLab n E) (h : S.IsSol L) (i : Fin n) (s : Fin 4) :
    L.uSlot i s = L.uSlot i (S.σ i 0) - S.tau (S.pairs L) i s := by
  have := S.slot_eq i (L.uSlot i) (h i).1 s
  simpa [tau, pairs] using this

lemma a_eq (L : ChainLab n E) (h : S.IsSol L) :
    ∀ j : Fin (n + 1), L.a j = S.railU (L.a 0) (S.pairs L) j := by
  intro j
  induction j using Fin.induction with
  | zero => rw [railU_zero]
  | succ i ih =>
    rw [railU_succ, ← ih]
    have h2 := S.uSlot_eq L h i 2
    have h3 := S.uSlot_eq L h i 3
    have e2 : L.uSlot i 2 = L.a i.castSucc := by simp [ChainLab.uSlot]
    have e3 : L.uSlot i 3 = L.a i.succ := by simp [ChainLab.uSlot]
    rw [e2] at h2; rw [e3] at h3
    rw [h3]
    have : L.uSlot i (S.σ i 0) = L.a i.castSucc + S.tau (S.pairs L) i 2 := by
      rw [h2]; abel
    rw [this]; abel


lemma b_eq (L : ChainLab n E) (h : S.IsSol L) :
    ∀ j : Fin (n + 1), L.a j - L.b j = S.epsF j • (L.a 0 - L.b 0) := by
  intro j
  induction j using Fin.induction with
  | zero => simp [epsF_zero]
  | succ i ih =>
    rw [epsF_succ, mul_comm, mul_smul, ← ih]
    have hu := (h i).1
    have hv := (h i).2
    have hd : S.sg i 2 • (L.a i.castSucc - L.b i.castSucc) + S.sg i 3 • (L.a i.succ - L.b i.succ) = 0 := by
      simp only [Fin.sum_univ_four, ChainLab.uSlot, ChainLab.vSlot] at hu hv
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hu hv
      rw [← sub_eq_zero] at hu hv
      rw [← sub_eq_zero.mpr (hu.trans hv.symm)]
      simp only [smul_sub]; abel
    have hsq := S.sg_sq i 3
    have h3 := congrArg (fun z => S.sg i 3 • z) hd
    simp only [smul_add, smul_zero, ← mul_smul] at h3
    rw [hsq, one_smul] at h3
    rw [eq_neg_of_add_eq_zero_right h3, neg_smul]

lemma inv_pairs (L : ChainLab n E) (h : S.IsSol L) :
    S.inv (L.a 0) (L.b 0) (S.pairs L) = L := by
  have hA := S.a_eq L h
  have hB := S.b_eq L h
  refine ChainLab.ext ?_ ?_ ?_
  · funext i k
    have e := S.uSlot_eq L h i (rungSlot k)
    have e2 := S.uSlot_eq L h i 2
    have hk : L.uSlot i (rungSlot k) = L.r i k := by
      fin_cases k <;> simp [ChainLab.uSlot, rungSlot]
    have h2 : L.uSlot i 2 = L.a i.castSucc := by simp [ChainLab.uSlot]
    rw [hk] at e
    rw [h2] at e2
    have : L.uSlot i (S.σ i 0) = L.a i.castSucc + S.tau (S.pairs L) i 2 := by
      rw [e2]; abel
    simp only [inv]
    rw [← hA i.castSucc, e, this]
  · funext j
    exact (hA j).symm
  · funext j
    have := hB j
    simp only [inv]
    rw [← hA j, ← this]; abel

/-- **The interior chart.** Solutions of the interior conservation equations correspond to
`(a_0, b_0, (x_i, y_i)_i)`. -/
def chartEquiv : {L : ChainLab n E // S.IsSol L} ≃ E × E × (Fin n → E × E) where
  toFun L := (L.1.a 0, L.1.b 0, S.pairs L.1)
  invFun c := ⟨S.inv c.1 c.2.1 c.2.2, S.isSol_inv _ _ _⟩
  left_inv L := Subtype.ext (S.inv_pairs L.1 L.2)
  right_inv c := by
    obtain ⟨a0, b0, P⟩ := c
    have hsol := S.isSol_inv a0 b0 P
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp [inv, railU_zero]
    · simp [inv, railU_zero, epsF_zero]
    · funext i
      have e := S.uSlot_eq _ hsol i
      have hh : ∀ s, (S.inv a0 b0 P).uSlot i s = S.railU a0 P i.castSucc + S.tau P i 2 - S.tau P i s :=
        S.inv_uSlot a0 b0 P i
      simp only [pairs, hh, tau_perm]
      simp [tvec]

end ChainSigns
end WaveTurbulence.LadderDecay
