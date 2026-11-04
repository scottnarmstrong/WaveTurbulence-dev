/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.CountLemmas.A23Half
public import WaveTurbulence.Foundations.WeylSums.ThreeVectorReduction

/-!
# The system `{(1,2,3),(1,4,5)}` of DH23 Lemma A.3(4), `γ > 1/2`: Lemma 2.1 reparametrization

DH23 (`Revision_Submit.tex`) L2093–L2096 (counteqn and the sign rules), L2106 (Lemma A.3(4)), L2110 (the
factorization); research note `docs/research/case4-gamma-above-half.txt` Lemma 2.1; referee check 4.2.

The vectors `k₁,…,k₅ = n₀/L,…,n₄/L ∈ ℤ_L^d` lie in unit balls around fixed `a₀,…,a₄`, and satisfy the two tuples
`A = (1,2,3)` and `B = (1,4,5)` of (counteqn) with signs `εA`, `εB`, windows `τ = δ⁻¹ L^{-2γ}`.

* `reparam_energy_identity`: `|kᵢ|² + |kⱼ|² − |kᵢ + kⱼ − k|² = |k|² − 2 (kᵢ − k)·(kⱼ − k)`. DH23 L2110 prints the
  factor `+2`; the correct factor is `−2` (CountLemmas HANDOFF erratum).
* `tupleEqn_normalize`: a tuple without three equal signs, multiplied by `±1`, reads `k_p + k_q − k_o = k`; if the
  shared entry `k₁` is not the odd one, it is listed first.
* The three forms (Lemma 2.1 (i)–(iv), with (iii) = (ii) after exchanging `A` and `B`, `v ↦ −v`), each an injection of
  the solution set into `coupledTripleSet`:
  - `ncard_le_coupled_cyclic`: `k₁` odd in both, `ζ = x + y − v − z`;
  - `ncard_le_coupled_mixed`: `k₁` odd in exactly one, `ζ = x + y − v`;
  - `ncard_le_coupled_anti`: `k₁` odd in neither, `ζ = x − v`.
* `system12345_bound`: `#{(1,2,3),(1,4,5)} ≤ C δ⁻² L^{3(d−γ) − γ₀ − κ(γ)}` for `1/2 < γ < 1`, for every
  pair of sign patterns without three equal signs in a tuple (36 pairs). DH23's rule that `k₁` carries opposite signs
  in `A` and `B` is not needed; the admissible pairs number 18 (`card_admissible12345`).
-/

public section

open Set

namespace WaveTurbulence.CountLemmas

variable {d : ℕ}

/-! ### The identity and the sets -/

/-- **Lemma 2.1 identity** (DH23 L2110 with the corrected sign): for `k_l = kᵢ + kⱼ − k`,
`|kᵢ|² + |kⱼ|² − |k_l|² = |k|² − 2 (kᵢ − k)·(kⱼ − k)`. -/
theorem reparam_energy_identity (ki kj k : Mom d) :
    ‖ki‖ ^ 2 + ‖kj‖ ^ 2 - ‖ki + kj - k‖ ^ 2 = ‖k‖ ^ 2 - 2 * inner ℝ (ki - k) (kj - k) := by
  obtain ⟨p, rfl⟩ : ∃ p, ki = p + k := ⟨ki - k, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, kj = q + k := ⟨kj - k, by abel⟩
  have e : p + k + (q + k) - k = (p + q) + k := by abel
  rw [e, add_sub_cancel_right, add_sub_cancel_right, norm_add_sq_real, norm_add_sq_real, norm_add_sq_real,
    norm_add_sq_real, inner_add_left]
  ring

/-- One tuple `(j₀^{ε₀}, j₁^{ε₁}, j₂^{ε₂})` of DH23 (counteqn) (L2094–L2095), `r = 3`, in integer coordinates
`k_j = n_j / L`, with right side `k = n_k / L`: `Σ εᵢ k_{jᵢ} = k` and `|Σ εᵢ |k_{jᵢ}|² − β| ≤ τ`. -/
@[expose] def TupleEqn (L : ℝ) (n : Fin 5 → Fin d → ℤ) (j : Fin 3 → Fin 5) (ε : Fin 3 → ℤˣ)
    (nk : Fin d → ℤ) (β τ : ℝ) : Prop :=
  ∑ i, (ε i : ℤ) • n (j i) = nk ∧
    |∑ i, ((ε i : ℤ) : ℝ) * ‖latticePoint L (n (j i))‖ ^ 2 - β| ≤ τ

/-- **The counting problem `{(1,2,3),(1,4,5)}` of DH23 Lemma A.3(4)** (L2106): indices `0,…,4` stand for
`k₁,…,k₅`; `|k_j − a_j| ≤ 1`; tuple `A = (1,2,3)` with signs `εA`, tuple `B = (1,4,5)` with signs `εB`. -/
@[expose] def system12345Set (L : ℝ) (a : Fin 5 → Mom d) (εA εB : Fin 3 → ℤˣ)
    (nA nB : Fin d → ℤ) (βA βB τ : ℝ) : Set (Fin 5 → Fin d → ℤ) :=
  {n | (∀ t, NearLattice L (a t) (n t)) ∧ TupleEqn L n ![0, 1, 2] εA nA βA τ ∧
    TupleEqn L n ![0, 3, 4] εB nB βB τ}

/-- DH23's sign rules (L2096) for `{(1,2,3),(1,4,5)}`: no tuple has three equal signs, and `k₁` has opposite signs
in the two tuples. -/
@[expose] def Admissible12345 (εA εB : Fin 3 → ℤˣ) : Prop :=
  ¬ (εA 0 = εA 1 ∧ εA 1 = εA 2) ∧ ¬ (εB 0 = εB 1 ∧ εB 1 = εB 2) ∧ εB 0 = -εA 0

instance (εA εB : Fin 3 → ℤˣ) : Decidable (Admissible12345 εA εB) := by
  unfold Admissible12345; infer_instance

/-- **The admissible sign patterns number 18** (the referee's check 4.2 says 16). -/
theorem card_admissible12345 :
    (Finset.univ.filter (fun ε : (Fin 3 → ℤˣ) × (Fin 3 → ℤˣ) => Admissible12345 ε.1 ε.2)).card = 18 := by
  decide

/-- A normalized tuple `k_p + k_q − k_o = k` with its energy window (Lemma 2.1). -/
@[expose] def NormTuple (L : ℝ) (n : Fin 5 → Fin d → ℤ) (p q o : Fin 5) (m : Fin d → ℤ)
    (β τ : ℝ) : Prop :=
  n p + n q - n o = m ∧
    |‖latticePoint L (n p)‖ ^ 2 + ‖latticePoint L (n q)‖ ^ 2 - ‖latticePoint L (n o)‖ ^ 2 - β| ≤ τ

/-! ### Normalization of one tuple -/

/-- A tuple whose signs are `s·(+,+,−)` on `(p,q,o)` is, after multiplication by `s`, the normalized tuple. -/
theorem normTuple_of_signs {L : ℝ} {n : Fin 5 → Fin d → ℤ} {j : Fin 3 → Fin 5} {ε : Fin 3 → ℤˣ}
    {nk : Fin d → ℤ} {β τ : ℝ} (s : ℤ) (hs : s * s = 1) (p q o : Fin 3)
    (hshape : (p = 1 ∧ q = 2 ∧ o = 0) ∨ (p = 0 ∧ q = 2 ∧ o = 1) ∨ (p = 0 ∧ q = 1 ∧ o = 2))
    (hp : (ε p : ℤ) = s) (hq : (ε q : ℤ) = s) (ho : (ε o : ℤ) = -s) (h : TupleEqn L n j ε nk β τ) :
    NormTuple L n (j p) (j q) (j o) (s • nk) (s * β) τ := by
  obtain ⟨hm, he⟩ := h
  rw [Fin.sum_univ_three] at hm he
  have hsR : (s : ℝ) * s = 1 := by exact_mod_cast hs
  -- the raw sums are `s` times the normalized ones
  have hm' : s • (n (j p) + n (j q) - n (j o)) = nk := by
    rw [← hm]
    rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      · rw [hp, hq, ho]; simp only [smul_add, smul_sub, neg_smul]; abel
  have he' : (s : ℝ) * (‖latticePoint L (n (j p))‖ ^ 2 + ‖latticePoint L (n (j q))‖ ^ 2 -
      ‖latticePoint L (n (j o))‖ ^ 2) - β =
      ((ε 0 : ℤ) : ℝ) * ‖latticePoint L (n (j 0))‖ ^ 2 + ((ε 1 : ℤ) : ℝ) * ‖latticePoint L (n (j 1))‖ ^ 2 +
        ((ε 2 : ℤ) : ℝ) * ‖latticePoint L (n (j 2))‖ ^ 2 - β := by
    rcases hshape with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      · rw [hp, hq, ho]; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [← hm', smul_smul, hs, one_smul]
  · have hrw : ‖latticePoint L (n (j p))‖ ^ 2 + ‖latticePoint L (n (j q))‖ ^ 2 -
        ‖latticePoint L (n (j o))‖ ^ 2 - (s : ℝ) * β =
        (s : ℝ) * ((s : ℝ) * (‖latticePoint L (n (j p))‖ ^ 2 + ‖latticePoint L (n (j q))‖ ^ 2 -
          ‖latticePoint L (n (j o))‖ ^ 2) - β) := by
      linear_combination (‖latticePoint L (n (j p))‖ ^ 2 + ‖latticePoint L (n (j q))‖ ^ 2 -
          ‖latticePoint L (n (j o))‖ ^ 2) * hsR.symm
    have habs : |(s : ℝ)| = 1 := by
      rcases mul_self_eq_one_iff.mp ((abs_mul_abs_self (s : ℝ)).trans hsR) with h | h
      · exact h
      · linarith only [h, abs_nonneg (s : ℝ)]
    rw [hrw, abs_mul, habs, one_mul, he']
    exact he

/-- **Normalization of a tuple without three equal signs** (Lemma 2.1, first step). -/
theorem tupleEqn_normalize (ε : Fin 3 → ℤˣ) (hε : ¬ (ε 0 = ε 1 ∧ ε 1 = ε 2)) :
    ∃ s : ℤ, ∃ p q o : Fin 3,
      ((p = 1 ∧ q = 2 ∧ o = 0) ∨ (p = 0 ∧ q = 2 ∧ o = 1) ∨ (p = 0 ∧ q = 1 ∧ o = 2)) ∧
      ∀ (L : ℝ) (n : Fin 5 → Fin d → ℤ) (j : Fin 3 → Fin 5) (nk : Fin d → ℤ) (β τ : ℝ),
        TupleEqn L n j ε nk β τ → NormTuple L n (j p) (j q) (j o) (s • nk) (s * β) τ := by
  rcases Int.units_eq_one_or (ε 0) with h0 | h0 <;> rcases Int.units_eq_one_or (ε 1) with h1 | h1 <;>
    rcases Int.units_eq_one_or (ε 2) with h2 | h2
  · exact absurd ⟨h0.trans h1.symm, h1.trans h2.symm⟩ hε
  · exact ⟨1, 0, 1, 2, by decide, fun L n j nk β τ =>
      normTuple_of_signs 1 (by norm_num) 0 1 2 (by decide) (by simp [h0]) (by simp [h1]) (by simp [h2])⟩
  · exact ⟨1, 0, 2, 1, by decide, fun L n j nk β τ =>
      normTuple_of_signs 1 (by norm_num) 0 2 1 (by decide) (by simp [h0]) (by simp [h2]) (by simp [h1])⟩
  · exact ⟨-1, 1, 2, 0, by decide, fun L n j nk β τ =>
      normTuple_of_signs (-1) (by norm_num) 1 2 0 (by decide) (by simp [h1]) (by simp [h2]) (by simp [h0])⟩
  · exact ⟨1, 1, 2, 0, by decide, fun L n j nk β τ =>
      normTuple_of_signs 1 (by norm_num) 1 2 0 (by decide) (by simp [h1]) (by simp [h2]) (by simp [h0])⟩
  · exact ⟨-1, 0, 2, 1, by decide, fun L n j nk β τ =>
      normTuple_of_signs (-1) (by norm_num) 0 2 1 (by decide) (by simp [h0]) (by simp [h2]) (by simp [h1])⟩
  · exact ⟨-1, 0, 1, 2, by decide, fun L n j nk β τ =>
      normTuple_of_signs (-1) (by norm_num) 0 1 2 (by decide) (by simp [h0]) (by simp [h1]) (by simp [h2])⟩
  · exact absurd ⟨h0.trans h1.symm, h1.trans h2.symm⟩ hε

/-! ### The three forms -/

/-- The unit ball moves with the lattice translation. -/
theorem nearLattice_sub {L : ℝ} {a : Mom d} {n : Fin d → ℤ} (m : Fin d → ℤ) (h : NearLattice L a n) :
    NearLattice L (a - latticePoint L m) (n - m) := by
  unfold NearLattice at h ⊢
  rwa [WeylSums.latticePoint_sub_eq, sub_sub_sub_cancel_right]

/-- A normalized tuple puts `(k_p − k)·(k_q − k)` in a window of the same length. -/
theorem normTuple_inner {L : ℝ} {n : Fin 5 → Fin d → ℤ} {p q o : Fin 5} {m : Fin d → ℤ} {β τ : ℝ}
    (h : NormTuple L n p q o m β τ) :
    |inner ℝ (latticePoint L (n p - m)) (latticePoint L (n q - m)) - (‖latticePoint L m‖ ^ 2 - β) / 2| ≤ τ := by
  obtain ⟨hm, he⟩ := h
  have ho : n o = n p + n q - m := by rw [← hm]; abel
  rw [ho, WeylSums.latticePoint_sub_eq, WeylSums.latticePoint_add_eq, reparam_energy_identity] at he
  rw [WeylSums.latticePoint_sub_eq, WeylSums.latticePoint_sub_eq]
  have hτ : 0 ≤ τ := (abs_nonneg _).trans he
  have heq : inner ℝ (latticePoint L (n p) - latticePoint L m) (latticePoint L (n q) - latticePoint L m) -
      (‖latticePoint L m‖ ^ 2 - β) / 2 =
      -((‖latticePoint L m‖ ^ 2 - 2 * inner ℝ (latticePoint L (n p) - latticePoint L m)
        (latticePoint L (n q) - latticePoint L m) - β) / 2) := by ring
  rw [heq, abs_neg, abs_div, abs_two]
  linarith only [he, hτ]

/-- Pointwise integer form of a vector identity. -/
theorem vec_eq_of_coord {u w : Fin d → ℤ} (h : ∀ i, u i = w i) : u = w := funext h

/-- **Form (i), cyclic**: `k₁` odd in both tuples (`p + q − 0` and `p' + q' − 0`); `x = k_p − a`, `y = k_q − a`,
`z = k_{p'} − b`, `ζ = x + y − v − z`, `v = b − a`. -/
theorem ncard_le_coupled_cyclic {L : ℝ} (hL : 0 < L) (a : Fin 5 → Mom d) (p q p' q' : Fin 5)
    (hcover : ∀ t : Fin 5, t = 0 ∨ t = p ∨ t = q ∨ t = p' ∨ t = q')
    (mA mB : Fin d → ℤ) (βA βB τ : ℝ) (S : Set (Fin 5 → Fin d → ℤ))
    (hS : ∀ n ∈ S, (∀ t, NearLattice L (a t) (n t)) ∧ NormTuple L n p q 0 mA βA τ ∧
      NormTuple L n p' q' 0 mB βB τ) :
    S.ncard ≤ (coupledTripleSet L (a p - latticePoint L mA) (a q - latticePoint L mA)
      (a p' - latticePoint L mB) (latticePoint L (mB - mA)) ((‖latticePoint L mA‖ ^ 2 - βA) / 2)
      ((‖latticePoint L mB‖ ^ 2 - βB) / 2) τ 2).ncard := by
  refine ncard_le_ncard_of_injOn (fun n => (n p - mA, n q - mA, n p' - mB)) ?_ ?_
    (finite_coupledTripleSet hL _ _ _ _ _ _ _ _)
  · intro n hn
    obtain ⟨hnear, hA, hB⟩ := hS n hn
    have hζ : n q' - mB = (n p - mA) + (n q - mA) - (mB - mA) - (n p' - mB) := by
      refine vec_eq_of_coord fun i => ?_
      have h1 := congrFun hA.1 i
      have h2 := congrFun hB.1 i
      simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
      omega
    refine ⟨nearLattice_sub mA (hnear p), nearLattice_sub mA (hnear q), nearLattice_sub mB (hnear p'),
      normTuple_inner hA, ?_⟩
    have hi := normTuple_inner hB
    rw [hζ, real_inner_comm] at hi
    simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, WeylSums.latticePoint_sub_eq,
      WeylSums.latticePoint_add_eq] using hi
  · intro n hn n' hn' hf
    obtain ⟨-, hA, hB⟩ := hS n hn
    obtain ⟨-, hA', hB'⟩ := hS n' hn'
    simp only [Prod.mk.injEq, sub_left_inj] at hf
    obtain ⟨hp, hq, hp'⟩ := hf
    have h0 : n 0 = n' 0 := by
      have e1 : n 0 = n p + n q - mA := by rw [← hA.1]; abel
      have e2 : n' 0 = n' p + n' q - mA := by rw [← hA'.1]; abel
      rw [e1, e2, hp, hq]
    have hq' : n q' = n' q' := by
      have e1 : n q' = mB + n 0 - n p' := by rw [← hB.1]; abel
      have e2 : n' q' = mB + n' 0 - n' p' := by rw [← hB'.1]; abel
      rw [e1, e2, h0, hp']
    funext t
    rcases hcover t with rfl | rfl | rfl | rfl | rfl
    exacts [h0, hp, hq, hp', hq']

/-- **Form (ii), mixed**: `k₁` odd in the first tuple (`p + q − 0`) and not in the second (`0 + j − l`);
`x = k_p − a`, `y = k_q − a`, `z = k_j − b`, `ζ = x + y − v`, `v = b − a`. Form (iii) is this with the tuples
exchanged. -/
theorem ncard_le_coupled_mixed {L : ℝ} (hL : 0 < L) (a : Fin 5 → Mom d) (p q j l : Fin 5)
    (hcover : ∀ t : Fin 5, t = 0 ∨ t = p ∨ t = q ∨ t = j ∨ t = l)
    (mA mB : Fin d → ℤ) (βA βB τ : ℝ) (S : Set (Fin 5 → Fin d → ℤ))
    (hS : ∀ n ∈ S, (∀ t, NearLattice L (a t) (n t)) ∧ NormTuple L n p q 0 mA βA τ ∧
      NormTuple L n 0 j l mB βB τ) :
    S.ncard ≤ (coupledTripleSet L (a p - latticePoint L mA) (a q - latticePoint L mA)
      (a j - latticePoint L mB) (latticePoint L (mB - mA)) ((‖latticePoint L mA‖ ^ 2 - βA) / 2)
      ((‖latticePoint L mB‖ ^ 2 - βB) / 2) τ 1).ncard := by
  refine ncard_le_ncard_of_injOn (fun n => (n p - mA, n q - mA, n j - mB)) ?_ ?_
    (finite_coupledTripleSet hL _ _ _ _ _ _ _ _)
  · intro n hn
    obtain ⟨hnear, hA, hB⟩ := hS n hn
    have hζ : n 0 - mB = (n p - mA) + (n q - mA) - (mB - mA) := by
      refine vec_eq_of_coord fun i => ?_
      have h1 := congrFun hA.1 i
      simp only [Pi.add_apply, Pi.sub_apply] at h1 ⊢
      omega
    refine ⟨nearLattice_sub mA (hnear p), nearLattice_sub mA (hnear q), nearLattice_sub mB (hnear j),
      normTuple_inner hA, ?_⟩
    have hi := normTuple_inner hB
    rw [hζ] at hi
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, WeylSums.latticePoint_sub_eq,
      WeylSums.latticePoint_add_eq] using hi
  · intro n hn n' hn' hf
    obtain ⟨-, hA, hB⟩ := hS n hn
    obtain ⟨-, hA', hB'⟩ := hS n' hn'
    simp only [Prod.mk.injEq, sub_left_inj] at hf
    obtain ⟨hp, hq, hj⟩ := hf
    have h0 : n 0 = n' 0 := by
      have e1 : n 0 = n p + n q - mA := by rw [← hA.1]; abel
      have e2 : n' 0 = n' p + n' q - mA := by rw [← hA'.1]; abel
      rw [e1, e2, hp, hq]
    have hl : n l = n' l := by
      have e1 : n l = n 0 + n j - mB := by rw [← hB.1]; abel
      have e2 : n' l = n' 0 + n' j - mB := by rw [← hB'.1]; abel
      rw [e1, e2, h0, hj]
    funext t
    rcases hcover t with rfl | rfl | rfl | rfl | rfl
    exacts [h0, hp, hq, hj, hl]

/-- **Form (iv), anti-parallel**: `k₁` odd in neither tuple (`0 + i − l` and `0 + j − l'`); `x = k₁ − a`,
`y = k_i − a`, `z = k_j − b`, `ζ = x − v`, `v = b − a`. -/
theorem ncard_le_coupled_anti {L : ℝ} (hL : 0 < L) (a : Fin 5 → Mom d) (i l j l' : Fin 5)
    (hcover : ∀ t : Fin 5, t = 0 ∨ t = i ∨ t = l ∨ t = j ∨ t = l')
    (mA mB : Fin d → ℤ) (βA βB τ : ℝ) (S : Set (Fin 5 → Fin d → ℤ))
    (hS : ∀ n ∈ S, (∀ t, NearLattice L (a t) (n t)) ∧ NormTuple L n 0 i l mA βA τ ∧
      NormTuple L n 0 j l' mB βB τ) :
    S.ncard ≤ (coupledTripleSet L (a 0 - latticePoint L mA) (a i - latticePoint L mA)
      (a j - latticePoint L mB) (latticePoint L (mB - mA)) ((‖latticePoint L mA‖ ^ 2 - βA) / 2)
      ((‖latticePoint L mB‖ ^ 2 - βB) / 2) τ 0).ncard := by
  refine ncard_le_ncard_of_injOn (fun n => (n 0 - mA, n i - mA, n j - mB)) ?_ ?_
    (finite_coupledTripleSet hL _ _ _ _ _ _ _ _)
  · intro n hn
    obtain ⟨hnear, hA, hB⟩ := hS n hn
    have hζ : n 0 - mB = (n 0 - mA) - (mB - mA) := by abel
    refine ⟨nearLattice_sub mA (hnear 0), nearLattice_sub mA (hnear i), nearLattice_sub mB (hnear j),
      normTuple_inner hA, ?_⟩
    have hi := normTuple_inner hB
    rw [hζ] at hi
    simpa only [Matrix.cons_val_zero, WeylSums.latticePoint_sub_eq] using hi
  · intro n hn n' hn' hf
    obtain ⟨-, hA, hB⟩ := hS n hn
    obtain ⟨-, hA', hB'⟩ := hS n' hn'
    simp only [Prod.mk.injEq, sub_left_inj] at hf
    obtain ⟨h0, hi, hj⟩ := hf
    have hl : n l = n' l := by
      have e1 : n l = n 0 + n i - mA := by rw [← hA.1]; abel
      have e2 : n' l = n' 0 + n' i - mA := by rw [← hA'.1]; abel
      rw [e1, e2, h0, hi]
    have hl' : n l' = n' l' := by
      have e1 : n l' = n 0 + n j - mB := by rw [← hB.1]; abel
      have e2 : n' l' = n' 0 + n' j - mB := by rw [← hB'.1]; abel
      rw [e1, e2, h0, hj]
    funext t
    rcases hcover t with rfl | rfl | rfl | rfl | rfl
    exacts [h0, hi, hl, hj, hl']

/-! ### The count -/

/-- **DH23 Lemma A.3(4), `{(1,2,3),(1,4,5)}`, `γ > 1/2`**:
`#{(1,2,3),(1,4,5)} ≤ C δ⁻² L^{3(d−γ) − γ₀ − κ(γ)}`, `γ₀ = 1 − γ`, `κ(γ) = min((2γ−1)/3, 1−γ)`, for all
sign patterns without three equal signs in a tuple (in particular the 18 admissible ones of L2096), all centers
`a_j`, all right sides `k_A, k_B ∈ ℤ_L^d` and all `β_A, β_B`. `C` is independent of `δ`. -/
theorem system12345_bound :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (1 / 2 : ℝ) 1 → ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1,
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ (a : Fin 5 → Mom d) (εA εB : Fin 3 → ℤˣ),
        ¬ (εA 0 = εA 1 ∧ εA 1 = εA 2) → ¬ (εB 0 = εB 1 ∧ εB 1 = εB 2) →
        ∀ (nA nB : Fin d → ℤ) (βA βB : ℝ),
          ((system12345Set L a εA εB nA nB βA βB (δ⁻¹ * L ^ (-2 * γ))).ncard : ℝ) ≤
            C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - kappaHalf γ) := by
  intro d hd γ hγ
  obtain ⟨C, hC, hbound⟩ := a23Half_bound d hd γ hγ
  refine ⟨C, hC, fun δ hδ => ?_⟩
  obtain ⟨L₁, hL₁⟩ := hbound δ hδ
  refine ⟨max L₁ 1, fun L hL a εA εB hεA hεB nA nB βA βB => ?_⟩
  have hLp : 0 < L := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hL)
  have hLL : L ≥ L₁ := (le_max_left _ _).trans hL
  set τ := δ⁻¹ * L ^ (-2 * γ)
  set S := system12345Set L a εA εB nA nB βA βB τ
  obtain ⟨sA, pA, qA, oA, hshA, hnA⟩ := tupleEqn_normalize (d := d) εA hεA
  obtain ⟨sB, pB, qB, oB, hshB, hnB⟩ := tupleEqn_normalize (d := d) εB hεB
  have hS : ∀ n ∈ S, (∀ t, NearLattice L (a t) (n t)) ∧
      NormTuple L n (![0, 1, 2] pA) (![0, 1, 2] qA) (![0, 1, 2] oA) (sA • nA) (sA * βA) τ ∧
      NormTuple L n (![0, 3, 4] pB) (![0, 3, 4] qB) (![0, 3, 4] oB) (sB • nB) (sB * βB) τ :=
    fun n hn => ⟨hn.1, hnA L n _ nA βA τ hn.2.1, hnB L n _ nB βB τ hn.2.2⟩
  rcases hshA with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases hshB with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  -- the nine (odd entry of `A`, odd entry of `B`) cases: (i) cyclic, (ii)/(iii) mixed, (iv) anti-parallel
  · -- (i): `k₁` odd in `A` and in `B`
    exact (Nat.cast_le.mpr (ncard_le_coupled_cyclic hLp a 1 2 3 4 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · -- (ii): `k₁` odd in `A` only
    exact (Nat.cast_le.mpr (ncard_le_coupled_mixed hLp a 1 2 4 3 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_mixed hLp a 1 2 3 4 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · -- (iii): `k₁` odd in `B` only (the tuples exchanged)
    exact (Nat.cast_le.mpr (ncard_le_coupled_mixed hLp a 3 4 2 1 (by decide) _ _ _ _ τ S
      fun n hn => ⟨(hS n hn).1, (hS n hn).2.2, (hS n hn).2.1⟩)).trans (hL₁ L hLL _ _ _ _ _ _ _)
  · -- (iv): `k₁` odd in neither
    exact (Nat.cast_le.mpr (ncard_le_coupled_anti hLp a 2 1 4 3 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_anti hLp a 2 1 3 4 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_mixed hLp a 3 4 1 2 (by decide) _ _ _ _ τ S
      fun n hn => ⟨(hS n hn).1, (hS n hn).2.2, (hS n hn).2.1⟩)).trans (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_anti hLp a 1 2 4 3 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)
  · exact (Nat.cast_le.mpr (ncard_le_coupled_anti hLp a 1 2 3 4 (by decide) _ _ _ _ τ S hS)).trans
      (hL₁ L hLL _ _ _ _ _ _ _)

end WaveTurbulence.CountLemmas
