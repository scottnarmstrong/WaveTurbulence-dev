/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ChainAlg
/-! # Local phases of the interior ladder chart (S3b LADDER-DECAY)

Under the interior chart, the quadratic phases `Gamma_{u_i}`, `Gamma_{v_i}` of an interior rung
are local: `2 x.y` and `-2 x.y + (linear in x,y) + const`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset

variable {n : ℕ} {E V : Type*} [AddCommGroup E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma norm_quad (A X Y : V) :
    ‖A‖ ^ 2 + ‖A - (X + Y)‖ ^ 2 - ‖A - X‖ ^ 2 - ‖A - Y‖ ^ 2 = 2 * inner ℝ X Y := by
  simp only [norm_sub_sq_real, inner_add_right]
  rw [norm_add_sq_real]
  ring

lemma vec_B (W0 W1 R0 R1 Q : V) (s2 s3 : ℝ) (hs2 : s2 * s2 = 1) (hs3 : s3 * s3 = 1)
    (h0 : s2 • R0 = -Q) (h1 : s3 • R1 = Q) :
    s2 * (‖W0 - R0‖ ^ 2 - ‖W0‖ ^ 2) + s3 * (‖W1 - R1‖ ^ 2 - ‖W1‖ ^ 2) =
      2 * inner ℝ (W0 - W1) Q + (s2 + s3) * ‖Q‖ ^ 2 := by
  have e0 : R0 = -(s2 • Q) := by
    have := congrArg (fun z => s2 • z) h0
    simp only [smul_smul, hs2, one_smul, smul_neg] at this
    exact this
  have e1 : R1 = s3 • Q := by
    have := congrArg (fun z => s3 • z) h1
    simp only [smul_smul, hs3, one_smul] at this
    exact this
  have n2 : ‖s2 • Q‖ ^ 2 = ‖Q‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, sq, hs2, one_mul]
  have n3 : ‖s3 • Q‖ ^ 2 = ‖Q‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, sq, hs3, one_mul]
  subst e0 e1
  rw [sub_neg_eq_add, norm_add_sq_real, norm_sub_sq_real, n2, n3, inner_sub_left,
    real_inner_smul_right, real_inner_smul_right]
  linear_combination (2 * inner ℝ W0 Q) * hs2 - (2 * inner ℝ W1 Q) * hs3

namespace ChainSigns
variable (S : ChainSigns n) (φ : E →+ V) (w : V)

/-- `Gamma` at the u-atom of interior rung `i` (labels `w + φ(label)`). -/
noncomputable def gammaU (L : ChainLab n E) (i : Fin n) : ℝ :=
  ∑ k, (S.sg i k : ℝ) * ‖w + φ (L.uSlot i k)‖ ^ 2

/-- `Gamma` at the v-atom of interior rung `i` (v signs are the negatives of the u signs). -/
noncomputable def gammaV (L : ChainLab n E) (i : Fin n) : ℝ :=
  ∑ k, -(S.sg i k : ℝ) * ‖w + φ (L.vSlot i k)‖ ^ 2

lemma sum_perm_real (i : Fin n) (f : Fin 4 → ℝ) :
    ∑ k, (S.sg i k : ℝ) * f k = f (S.σ i 0) + f (S.σ i 1) - f (S.σ i 2) - f (S.σ i 3) := by
  rw [← Equiv.sum_comp (S.σ i)]
  rw [Fin.sum_univ_four]
  obtain ⟨h0, h1⟩ := S.plus i
  obtain ⟨h2, h3⟩ := S.minus i
  rw [h0, h1, h2, h3]
  push_cast
  ring

theorem gammaU_eq (L : ChainLab n E) (h : S.IsSol L) (i : Fin n) :
    S.gammaU φ w L i = 2 * inner ℝ (φ (S.pairs L i).1) (φ (S.pairs L i).2) := by
  unfold gammaU
  rw [S.sum_perm_real i (fun k => ‖w + φ (L.uSlot i k)‖ ^ 2)]
  have e1 := S.slot_eq i (L.uSlot i) (h i).1 (S.σ i 1)
  have e2 := S.slot_eq i (L.uSlot i) (h i).1 (S.σ i 2)
  have e3 := S.slot_eq i (L.uSlot i) (h i).1 (S.σ i 3)
  simp only [Equiv.symm_apply_apply, tvec] at e1 e2 e3
  simp only [Matrix.cons_val_one, Matrix.cons_val] at e1 e2 e3
  simp only [pairs]
  rw [e1, e2, e3]
  have := norm_quad (w + φ (L.uSlot i (S.σ i 0)))
    (φ (L.uSlot i (S.σ i 0) - L.uSlot i (S.σ i 2))) (φ (L.uSlot i (S.σ i 0) - L.uSlot i (S.σ i 3)))
  simp only [map_sub, map_add] at this ⊢
  convert this using 3 <;> abel_nf


/-- The flux `q_i = s_3 (a_{i+1} - b_{i+1})` carried by the rails above interior rung `i`. -/
def qrel (L : ChainLab n E) (i : Fin n) : E := S.sg i 3 • (L.a i.succ - L.b i.succ)

lemma rail_rel (L : ChainLab n E) (h : S.IsSol L) (i : Fin n) :
    S.sg i 2 • (L.a i.castSucc - L.b i.castSucc) + S.sg i 3 • (L.a i.succ - L.b i.succ) = 0 := by
  have hu := (h i).1
  have hv := (h i).2
  simp only [Fin.sum_univ_four, ChainLab.uSlot, ChainLab.vSlot] at hu hv
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hu hv
  rw [← sub_eq_zero] at hu hv
  rw [← sub_eq_zero.mpr (hu.trans hv.symm)]
  simp only [smul_sub]; abel

lemma in_rail (L : ChainLab n E) (h : S.IsSol L) (i : Fin n) :
    S.sg i 2 • (L.a i.castSucc - L.b i.castSucc) = - S.qrel L i := by
  have := S.rail_rel L h i
  unfold qrel
  rw [eq_neg_iff_add_eq_zero]
  exact this

lemma qrel_succ (L : ChainLab n E) (h : S.IsSol L) (i j : Fin n) (hij : i.1 + 1 = j.1) :
    S.qrel L j = S.qrel L i := by
  have h1 := S.in_rail L h j
  have hl := S.link i j hij
  have hs : j.castSucc = i.succ := by ext; simp; omega
  rw [hl, hs, neg_smul] at h1
  exact (neg_inj.mp h1).symm

lemma qrel_const (L : ChainLab n E) (h : S.IsSol L) (i j : Fin n) : S.qrel L i = S.qrel L j := by
  have key : ∀ k : ℕ, ∀ hk : k < n, ∀ hn : 0 < n, S.qrel L ⟨k, hk⟩ = S.qrel L ⟨0, hn⟩ := by
    intro k
    induction k with
    | zero => intro hk hn; rfl
    | succ k ih =>
      intro hk hn
      rw [S.qrel_succ L h ⟨k, by omega⟩ ⟨k + 1, hk⟩ rfl]
      exact ih _ _
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  rw [key i.1 i.2 hn, key j.1 j.2 hn]


lemma a_succ_sub (L : ChainLab n E) (h : S.IsSol L) (i : Fin n) :
    L.a i.succ - L.a i.castSucc = S.tau (S.pairs L) i 2 - S.tau (S.pairs L) i 3 := by
  have h2 := S.uSlot_eq L h i 2
  have h3 := S.uSlot_eq L h i 3
  have e2 : L.uSlot i 2 = L.a i.castSucc := by simp [ChainLab.uSlot]
  have e3 : L.uSlot i 3 = L.a i.succ := by simp [ChainLab.uSlot]
  rw [e2] at h2; rw [e3] at h3
  rw [h3, h2]; abel

theorem gammaV_eq (L : ChainLab n E) (h : S.IsSol L) (i : Fin n) :
    S.gammaV φ w L i =
      -(2 * inner ℝ (φ (S.pairs L i).1) (φ (S.pairs L i).2)) -
        2 * inner ℝ (φ (S.tau (S.pairs L) i 3 - S.tau (S.pairs L) i 2)) (φ (S.qrel L i)) -
          ((S.sg i 2 : ℝ) + (S.sg i 3 : ℝ)) * ‖φ (S.qrel L i)‖ ^ 2 := by
  have hGV : S.gammaV φ w L i = -S.gammaU φ w L i -
      ((S.sg i 2 : ℝ) * (‖w + φ (L.b i.castSucc)‖ ^ 2 - ‖w + φ (L.a i.castSucc)‖ ^ 2) +
        (S.sg i 3 : ℝ) * (‖w + φ (L.b i.succ)‖ ^ 2 - ‖w + φ (L.a i.succ)‖ ^ 2)) := by
    unfold gammaV gammaU
    simp only [Fin.sum_univ_four, ChainLab.uSlot, ChainLab.vSlot]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  rw [hGV, S.gammaU_eq φ w L h i]
  have hb : ∀ j : Fin (n + 1), w + φ (L.b j) = (w + φ (L.a j)) - φ (L.a j - L.b j) := by
    intro j; simp only [map_sub]; abel
  rw [hb i.castSucc, hb i.succ]
  have h0 : (S.sg i 2 : ℝ) • φ (L.a i.castSucc - L.b i.castSucc) = -φ (S.qrel L i) := by
    rw [Int.cast_smul_eq_zsmul, ← map_zsmul, S.in_rail L h i, map_neg]
  have h1 : (S.sg i 3 : ℝ) • φ (L.a i.succ - L.b i.succ) = φ (S.qrel L i) := by
    rw [Int.cast_smul_eq_zsmul, ← map_zsmul]; rfl
  have hv := vec_B (w + φ (L.a i.castSucc)) (w + φ (L.a i.succ)) _ _ _ _ _
    (by exact_mod_cast S.sg_sq i 2) (by exact_mod_cast S.sg_sq i 3) h0 h1
  have hd : (w + φ (L.a i.castSucc)) - (w + φ (L.a i.succ)) =
      φ (S.tau (S.pairs L) i 3 - S.tau (S.pairs L) i 2) := by
    have := S.a_succ_sub L h i
    have h' : L.a i.castSucc - L.a i.succ = S.tau (S.pairs L) i 3 - S.tau (S.pairs L) i 2 := by
      rw [← neg_sub, this]; abel
    rw [← h']; simp only [map_sub]; abel
  rw [hd] at hv
  linarith

end ChainSigns
end WaveTurbulence.LadderDecay
