/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.GenIso

/-!
# Generation of closures (N2 Lemma 1.7; M4 §5.4 Lemma 1.7′, confluence-free)

`closure_generation`: a multigraph `C` with at most two triple bonds that (Y2)-reduces to a doubled triangle is
isomorphic to `genC p` for valid parameters `p`, i.e. to `T`, `Z_k(T, ℓ)` or `Z_{k'}(Z_k(T, ℓ), ℓ')`.

The proof is M4's: reverse the given (Y2)-path; each reversed step is a (Z1) move; a move on a non-triple bond
starts a ladder (at most two starts, by the triple count), every other move extends the ladder of the triple bond
it acts on. On the instance side this is `gen_step`: one (Z1) move on `genC p₁` is isomorphic to `genC p`.
Extending the first ladder while a second one exists needs only the commutation `ladder_z1_comm` (the ladders use
disjoint names). No confluence, no canonical forms.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine

/-! ## Commuting a (Z1) move through a ladder -/

theorem ladder_z1_comm : ∀ (k : ℕ) {E : Edges} {x₀ y₀ M t₁ t₂ N : ℕ}
    (_h0 : mult E x₀ y₀ ≠ 0) (_ht : mult E t₁ t₂ ≠ 0) (_hne : s(x₀, y₀) ≠ s(t₁, t₂))
    (_hF : Fresh k E M) (_hN : ¬ InEnds E N) (_hN1 : ¬ InEnds E (N + 1))
    (_hNM : ¬ IsNew k M N) (_hNM1 : ¬ IsNew k M (N + 1)),
    SameMult (z1 (ladder k E x₀ y₀ M) t₁ t₂ N (N + 1)) (ladder k (z1 E t₁ t₂ N (N + 1)) x₀ y₀ M)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => SameMult.refl _
  | k + 1, E, x₀, y₀, M, t₁, t₂, N, h0, ht, hne, hF, hN, hN1, hNM, hNM1 => by
    simp only [ladder]
    have hM : ¬ InEnds E M := hF M ⟨0, by omega, Or.inl (by omega)⟩
    have hM1 : ¬ InEnds E (M + 1) := hF (M + 1) ⟨0, by omega, Or.inr (by omega)⟩
    have ht1 := (inEnds_of_mult_ne_zero ht).1
    have ht2 := (inEnds_of_mult_ne_zero ht).2
    have hx0 := (inEnds_of_mult_ne_zero h0).1
    have hy0 := (inEnds_of_mult_ne_zero h0).2
    have neq : ∀ z w, InEnds E z → ¬ InEnds E w → z ≠ w := fun z w hz hw h => hw (h ▸ hz)
    have hNM' : N ≠ M ∧ N ≠ M + 1 ∧ ¬ IsNew k (M + 4) N := by
      refine ⟨fun h => hNM (isNew_succ.mpr (Or.inl h)), fun h => hNM (isNew_succ.mpr (Or.inr (Or.inl h))),
        fun h => hNM (isNew_succ.mpr (Or.inr (Or.inr h)))⟩
    have hNM1' : N + 1 ≠ M ∧ N + 1 ≠ M + 1 ∧ ¬ IsNew k (M + 4) (N + 1) := by
      refine ⟨fun h => hNM1 (isNew_succ.mpr (Or.inl h)), fun h => hNM1 (isNew_succ.mpr (Or.inr (Or.inl h))),
        fun h => hNM1 (isNew_succ.mpr (Or.inr (Or.inr h)))⟩
    set E' := z1 E x₀ y₀ M (M + 1) with hE'
    have hE'MM : mult E' M (M + 1) ≠ 0 := z1_ne_zero_new E x₀ y₀ M (M + 1) h0
    have hE't : mult E' t₁ t₂ ≠ 0 := by
      have := mult_z1' E x₀ y₀ M (M + 1) t₁ t₂ h0
      rw [← hE'] at this
      rw [if_neg (fun h => hne h.symm), z1New_zero (neq _ _ ht1 hM) (neq _ _ ht1 hM1) (neq _ _ ht2 hM)
        (neq _ _ ht2 hM1)] at this
      omega
    have hMt : s(M, M + 1) ≠ s(t₁, t₂) := by
      have := neq _ _ ht1 hM; have := neq _ _ ht1 hM1; have := neq _ _ ht2 hM; have := neq _ _ ht2 hM1
      rw [Ne, Sym2.eq_iff]; omega
    have hF' : Fresh k E' (M + 4) := by
      intro z hz hz'
      rcases inEnds_z1 h0 hz' with h | h | h
      · exact hF z (isNew_succ.mpr (Or.inr (Or.inr hz))) h
      · obtain ⟨i, _, h'⟩ := hz; omega
      · obtain ⟨i, _, h'⟩ := hz; omega
    have hNE' : ¬ InEnds E' N := by
      intro h; rcases inEnds_z1 h0 h with h | h | h
      · exact hN h
      · exact hNM'.1 h
      · exact hNM'.2.1 h
    have hN1E' : ¬ InEnds E' (N + 1) := by
      intro h; rcases inEnds_z1 h0 h with h | h | h
      · exact hN1 h
      · exact hNM1'.1 h
      · exact hNM1'.2.1 h
    have ih := ladder_z1_comm k hE'MM hE't hMt hF' hNE' hN1E' hNM'.2.2 hNM1'.2.2
    refine ih.trans (ladder_congr k ?_ ?_)
    · refine z1_comm E x₀ y₀ t₁ t₂ M (M + 1) N (N + 1) h0 ht (fun h => absurd h hne) ?_ ?_
      · exact z1New_zero (neq _ _ ht1 hM) (neq _ _ ht1 hM1) (neq _ _ ht2 hM) (neq _ _ ht2 hM1)
      · exact z1New_zero (neq _ _ hx0 hN) (neq _ _ hx0 hN1) (neq _ _ hy0 hN) (neq _ _ hy0 hN1)
    · have := mult_z1' E' t₁ t₂ N (N + 1) M (M + 1) hE't
      rw [if_neg hMt] at this
      omega

/-! ## Facts about the generated closures -/

theorem gen1_zero : gen1 0 = tri := rfl

theorem gen1_succ (k : ℕ) : gen1 (k + 2) = z1 (gen1 (k + 1)) (4 * k + 3) (4 * k + 4) (4 * k + 7) (4 * k + 8) := by
  unfold gen1
  rw [ladder_succ (k + 1) tri 0 1 3]
  simp only [lastPair, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  congr 1 <;> ring

theorem gen1_one : gen1 1 = z1 tri 0 1 3 4 := rfl

theorem gen1_inEnds_lt {k z : ℕ} (h : InEnds (gen1 k) z) : z < 4 * k + 3 := by
  rcases gen1_ends h with h | ⟨i, hi, h⟩ <;> omega

theorem genC_second_succ (E : Edges) (x₀ y₀ k' : ℕ) :
    ladder (k' + 2) E x₀ y₀ 5 = z1 (ladder (k' + 1) E x₀ y₀ 5) (4 * k' + 5) (4 * k' + 6) (4 * k' + 9) (4 * k' + 10) := by
  rw [ladder_succ (k' + 1) E x₀ y₀ 5]
  simp only [lastPair, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  congr 1 <;> ring

/-- Relabelling the two non-standard starts of the first ladder (`T` is symmetric). -/
def swapAB (a b : ℕ) (z : ℕ) : ℕ := if z = a then b else if z = b then a else z

theorem swapAB_invol (a b : ℕ) (z : ℕ) : swapAB a b (swapAB a b z) = z := by
  unfold swapAB; split_ifs <;> omega

theorem tri_start_02 : SameMult (mapE (swapAB 1 2) (z1 tri 0 2 3 4)) (gen1 1) :=
  sameMult_of_perm (by decide)

theorem tri_start_21 : SameMult (mapE (swapAB 0 2) (z1 tri 2 1 3 4)) (gen1 1) :=
  sameMult_of_perm (by decide)

/-! ## One reversed step on the generated family -/


theorem gen_step (p₁ : CParam) (hp₁ : p₁.Valid) (x y : ℕ) (hxy : mult (genC p₁) x y ≠ 0) (hne : x ≠ y)
    (hτ : ∀ N, ¬ InEnds (genC p₁) N → ¬ InEnds (genC p₁) (N + 1) →
      AtMostTwoTriplesE (z1 (genC p₁) x y N (N + 1))) :
    ∃ x' y' N : ℕ, ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧ ¬ InEnds (genC p₁) N ∧
      ¬ InEnds (genC p₁) (N + 1) ∧ ∃ p : CParam, p.Valid ∧
        Nonempty (Iso (ofEdges (z1 (genC p₁) x' y' N (N + 1))) (genC p)) := by
  have hx := (inEnds_of_mult_ne_zero hxy).1
  have hy := (inEnds_of_mult_ne_zero hxy).2
  rcases p₁ with ⟨k, _ | ⟨x₀, y₀, k'⟩⟩
  · -- one ladder (or `T`)
    simp only [genC] at hxy hx hy hτ ⊢
    rcases k with _ | k
    · -- `T`: start the first ladder
      rw [gen1_zero] at hxy hx hy ⊢
      have hx2 := inEnds_tri.mp hx
      have hy2 := inEnds_tri.mp hy
      have f3 : ¬ InEnds tri 3 := fun h => absurd (inEnds_tri.mp h) (by omega)
      have f4 : ¬ InEnds tri 4 := fun h => absurd (inEnds_tri.mp h) (by omega)
      have h01 : Nonempty (Iso (ofEdges (z1 tri 0 1 3 4)) (genC ⟨1, none⟩)) := ⟨Iso.refl _⟩
      have h02 : Nonempty (Iso (ofEdges (z1 tri 0 2 3 4)) (genC ⟨1, none⟩)) :=
        ⟨(Iso.ofInvolution (swapAB 1 2) (swapAB_invol 1 2) _).ofSame tri_start_02⟩
      have h21 : Nonempty (Iso (ofEdges (z1 tri 2 1 3 4)) (genC ⟨1, none⟩)) :=
        ⟨(Iso.ofInvolution (swapAB 0 2) (swapAB_invol 0 2) _).ofSame tri_start_21⟩
      interval_cases x <;> interval_cases y <;> first
        | exact absurd rfl hne
        | exact ⟨0, 1, 3, by omega, f3, f4, ⟨1, none⟩, trivial, h01⟩
        | exact ⟨0, 2, 3, by omega, f3, f4, ⟨1, none⟩, trivial, h02⟩
        | exact ⟨2, 1, 3, by omega, f3, f4, ⟨1, none⟩, trivial, h21⟩
    · by_cases ht : s(x, y) = s(4 * k + 3, 4 * k + 4)
      · -- extend the first ladder
        have f7 : ¬ InEnds (gen1 (k + 1)) (4 * k + 7) := fun h => absurd (gen1_inEnds_lt h) (by omega)
        have f8 : ¬ InEnds (gen1 (k + 1)) (4 * k + 7 + 1) := fun h => absurd (gen1_inEnds_lt h) (by omega)
        refine ⟨4 * k + 3, 4 * k + 4, 4 * k + 7, ?_, f7, f8, ⟨k + 2, none⟩, trivial, ?_⟩
        · rw [Sym2.eq_iff] at ht; omega
        · simp only [genC]; rw [gen1_succ]; exact ⟨Iso.refl _⟩
      · -- start the second ladder
        have hle : mult (gen1 (k + 1)) x y ≤ 2 := gen1_le_two k ht
        have f5 : ¬ InEnds (gen1 (k + 1)) 5 := fresh_second (k + 1) 1 5 ⟨0, by omega, Or.inl rfl⟩
        have f6 : ¬ InEnds (gen1 (k + 1)) (5 + 1) := fresh_second (k + 1) 1 6 ⟨0, by omega, Or.inr rfl⟩
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · refine ⟨x, y, 5, Or.inl ⟨rfl, rfl⟩, f5, f6, ⟨k + 1, some (x, y, 1)⟩, ?_, ⟨Iso.refl _⟩⟩
          exact ⟨Nat.succ_le_succ (Nat.zero_le _), le_refl 1, hlt, hxy, hle⟩
        · refine ⟨y, x, 5, Or.inr ⟨rfl, rfl⟩, f5, f6, ⟨k + 1, some (y, x, 1)⟩, ?_, ⟨Iso.refl _⟩⟩
          exact ⟨Nat.succ_le_succ (Nat.zero_le _), le_refl 1, hlt, by rw [mult_comm]; exact hxy, by rw [mult_comm]; exact hle⟩
  · -- two ladders: the move must extend one of them
    simp only [CParam.Valid] at hp₁
    obtain ⟨hk, hk', hlt₀, h0, h0le⟩ := hp₁
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    simp only [genC] at hxy hx hy hτ ⊢
    set E := gen1 (k + 1) with hE
    have hF : Fresh (k' + 1) E 5 := fresh_second (k + 1) (k' + 1)
    have hx0 := (inEnds_of_mult_ne_zero h0).1
    have hy0 := (inEnds_of_mult_ne_zero h0).2
    have hends : ∀ z, InEnds (ladder (k' + 1) E x₀ y₀ 5) z →
        z ≤ 2 ∨ IsNew (k + 1) 3 z ∨ IsNew (k' + 1) 5 z := by
      intro z hz
      rcases ladder_ends (k' + 1) h0 hz with h | h
      · rcases gen1_ends h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    -- the triple bonds `t₁` (first ladder) and `t₂` (second ladder)
    have ht₁E : mult E (4 * k + 3) (4 * k + 4) = 3 := gen1_triple k
    have hne₀ : s(x₀, y₀) ≠ s(4 * k + 3, 4 * k + 4) := by
      intro h; have := ht₁E; rw [mult_eq_count, ← h, ← mult_eq_count] at this; omega
    have ht₁ : mult (ladder (k' + 1) E x₀ y₀ 5) (4 * k + 3) (4 * k + 4) = 3 := by
      have := ladder_old (k' + 1) (x := x₀) (y := y₀) (N := 5) (u := 4 * k + 3) (v := 4 * k + 4) h0
        (by rintro ⟨i, _, h⟩; omega) (by rintro ⟨i, _, h⟩; omega)
      rw [if_neg (fun h => hne₀ h.2.symm), ht₁E] at this; omega
    have ht₂ : mult (ladder (k' + 1) E x₀ y₀ 5) (4 * k' + 5) (4 * k' + 6) = 3 := by
      have := ladder_newest k' h0 hF
      rw [show 5 + 4 * k' = 4 * k' + 5 by ring, show 4 * k' + 5 + 1 = 4 * k' + 6 by ring] at this
      exact this
    by_cases h2 : s(x, y) = s(4 * k' + 5, 4 * k' + 6)
    · -- extend the second ladder
      have fN : ¬ InEnds (ladder (k' + 1) E x₀ y₀ 5) (4 * k' + 9) := by
        intro h; rcases hends _ h with h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> omega
      have fN1 : ¬ InEnds (ladder (k' + 1) E x₀ y₀ 5) (4 * k' + 9 + 1) := by
        intro h; rcases hends _ h with h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> omega
      refine ⟨4 * k' + 5, 4 * k' + 6, 4 * k' + 9, ?_, fN, fN1, ⟨k + 1, some (x₀, y₀, k' + 2)⟩,
        ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_succ (Nat.zero_le _), hlt₀, h0, h0le⟩, ?_⟩
      · rw [Sym2.eq_iff] at h2; omega
      · simp only [genC]; rw [genC_second_succ]; exact ⟨Iso.refl _⟩
    by_cases h1 : s(x, y) = s(4 * k + 3, 4 * k + 4)
    · -- extend the first ladder (commute the move through the second ladder)
      have fN : ¬ InEnds E (4 * k + 7) := fun h => absurd (gen1_inEnds_lt h) (by omega)
      have fN1 : ¬ InEnds E (4 * k + 7 + 1) := fun h => absurd (gen1_inEnds_lt h) (by omega)
      have nN : ¬ IsNew (k' + 1) 5 (4 * k + 7) := by rintro ⟨i, _, h⟩; omega
      have nN1 : ¬ IsNew (k' + 1) 5 (4 * k + 7 + 1) := by rintro ⟨i, _, h⟩; omega
      have fN' : ¬ InEnds (ladder (k' + 1) E x₀ y₀ 5) (4 * k + 7) := by
        intro h; rcases hends _ h with h | ⟨i, hi, h⟩ | h
        · omega
        · omega
        · exact nN h
      have fN1' : ¬ InEnds (ladder (k' + 1) E x₀ y₀ 5) (4 * k + 7 + 1) := by
        intro h; rcases hends _ h with h | ⟨i, hi, h⟩ | h
        · omega
        · omega
        · exact nN1 h
      have hcomm := ladder_z1_comm (k' + 1) h0 (by rw [ht₁E]; omega) hne₀ hF fN fN1 nN nN1
      -- validity of the new parameters
      have hmult : mult (gen1 (k + 2)) x₀ y₀ = mult E x₀ y₀ := by
        rw [gen1_succ]
        have := mult_z1' E (4 * k + 3) (4 * k + 4) (4 * k + 7) (4 * k + 8) x₀ y₀ (by rw [ht₁E]; omega)
        have hx7 := gen1_inEnds_lt hx0
        have hy7 := gen1_inEnds_lt hy0
        rw [if_neg hne₀, z1New_zero (by omega) (by omega) (by omega) (by omega)] at this
        omega
      refine ⟨4 * k + 3, 4 * k + 4, 4 * k + 7, ?_, fN', fN1', ⟨k + 2, some (x₀, y₀, k' + 1)⟩,
        ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_succ (Nat.zero_le _), hlt₀, by rw [hmult]; exact h0,
          by rw [hmult]; exact h0le⟩, ?_⟩
      · rw [Sym2.eq_iff] at h1; omega
      · simp only [genC]; rw [gen1_succ]; exact ⟨Iso.ofSameMult hcomm⟩
    · -- a third triple bond: impossible
      exfalso
      set N₀ := 4 * k + 4 * k' + 11
      have f0 : ¬ InEnds (ladder (k' + 1) E x₀ y₀ 5) N₀ := by
        intro h; rcases hends _ h with h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> omega
      have f1 : ¬ InEnds (ladder (k' + 1) E x₀ y₀ 5) (N₀ + 1) := by
        intro h; rcases hends _ h with h | ⟨i, hi, h⟩ | ⟨i, hi, h⟩ <;> omega
      have hxN : x ≠ N₀ := fun h => f0 (h ▸ hx)
      have hxN1 : x ≠ N₀ + 1 := fun h => f1 (h ▸ hx)
      have hyN : y ≠ N₀ := fun h => f0 (h ▸ hy)
      have hyN1 : y ≠ N₀ + 1 := fun h => f1 (h ▸ hy)
      have T0 : mult (z1 (ladder (k' + 1) E x₀ y₀ 5) x y N₀ (N₀ + 1)) N₀ (N₀ + 1) = 3 := by
        have := mult_z1' (ladder (k' + 1) E x₀ y₀ 5) x y N₀ (N₀ + 1) N₀ (N₀ + 1) hxy
        rw [mult_eq_zero_of_not_inEnds f0, if_neg (sym2_ne_of_left (Ne.symm hxN) (Ne.symm hyN)),
          z1New_a_b hxN1 hyN] at this
        omega
      have T1 : mult (z1 (ladder (k' + 1) E x₀ y₀ 5) x y N₀ (N₀ + 1)) (4 * k + 3) (4 * k + 4) = 3 := by
        have := mult_z1' (ladder (k' + 1) E x₀ y₀ 5) x y N₀ (N₀ + 1) (4 * k + 3) (4 * k + 4) hxy
        rw [if_neg (fun h => h1 h.symm), z1New_zero (by omega) (by omega) (by omega) (by omega)] at this
        omega
      have T2 : mult (z1 (ladder (k' + 1) E x₀ y₀ 5) x y N₀ (N₀ + 1)) (4 * k' + 5) (4 * k' + 6) = 3 := by
        have := mult_z1' (ladder (k' + 1) E x₀ y₀ 5) x y N₀ (N₀ + 1) (4 * k' + 5) (4 * k' + 6) hxy
        rw [if_neg (fun h => h2 h.symm), z1New_zero (by omega) (by omega) (by omega) (by omega)] at this
        omega
      rcases hτ N₀ f0 f1 _ _ _ _ _ _ T0 T1 T2 with h | h | h <;> rw [Sym2.eq_iff] at h <;> omega

/-! ## The generation theorem for closures -/

variable {V : Type*} [DecidableEq V]

/-- **N2 Lemma 1.7 for closures (M4 Lemma 1.7′, confluence-free).** A multigraph with at most two triple
bonds that (Y2)-reduces to a doubled triangle is isomorphic to `genC p` for valid parameters `p`: to `T`,
`Z_k(T, ℓ)` or `Z_{k'}(Z_k(T, ℓ), ℓ')` with `ℓ'` a non-triple bond of `Z_k(T, ℓ)`. -/
theorem closure_generation {C T' : UMultigraph V} (h : Relation.ReflTransGen Y2Step C T')
    (hT : IsDoubledTriangle T') (h2 : AtMostTwoTriples C) :
    ∃ p : CParam, p.Valid ∧ Nonempty (Iso C (genC p)) := by
  revert h2
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · intro _
    exact ⟨⟨0, none⟩, trivial, iso_tri hT⟩
  · intro C C₁ hstep _ ih h2
    obtain ⟨p₁, hp₁, ⟨φ⟩⟩ := ih (atMostTwoTriples_of_y2 hstep h2)
    obtain ⟨x, y, hxy, hne, hiso⟩ := iso_of_y2 hstep φ
    have hτ : ∀ N, ¬ InEnds (genC p₁) N → ¬ InEnds (genC p₁) (N + 1) →
        AtMostTwoTriplesE (z1 (genC p₁) x y N (N + 1)) :=
      fun N hN hN1 => atMostTwoTriplesE_of_iso (hiso N hN hN1).1.some h2
    obtain ⟨x', y', N, hor, hN, hN1, p, hp, ⟨ψ⟩⟩ := gen_step p₁ hp₁ x y hxy hne hτ
    rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨p, hp, ⟨(hiso N hN hN1).1.some.trans ψ⟩⟩
    · exact ⟨p, hp, ⟨(hiso N hN hN1).2.some.trans ψ⟩⟩

end WaveTurbulence.TVine.Checker
