/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Counts
/-! **L6E GHOST, part 3: two slabs for a transverse pair of `α`-ghosts** (M1-R2 Theorem 6.1 (b), Lemma 5.1).

`card_twoSlab_vec`: integer normals `na`, `nb` (`|nb| ≤ |na|`) with `θ²|na|²|nb|² ≤ |na|²|nb|² - ⟨na,nb⟩²`: the two
centred slabs of radius `r` in the box `[-m, m]^d` hold at most `twoSlabX d m r ℓa ℓb θ` points (`ℓ ≤ |n|`).
`card_P5_two`: the triple count of three singleton blocks (all cuts `β`) with two transverse `α`-ghost gaps. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCount.TriData

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The real bound of the two-slab count (`r` the slab radius, `ℓa, ℓb` lower bounds of the normals, `θ` the angle
bound, box `[-m, m]^d`). -/
noncomputable def twoSlabX (d m : ℕ) (r ℓa ℓb θ : ℝ) : ℝ :=
  (4 * r ^ 2 * (d : ℝ) ^ 2 * (1 + d) / (θ * ℓa * ℓb) + 2 * r * d * (1 + d) / θ * (1 / ℓa + 1 / ℓb) + 1) *
    (2 * (m : ℝ) + 1) ^ (d - 2)

theorem twoSlabX_comm (d m : ℕ) (r ℓa ℓb θ : ℝ) : twoSlabX d m r ℓa ℓb θ = twoSlabX d m r ℓb ℓa θ := by
  unfold twoSlabX; ring

theorem le_of_sq_le_sq' {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) (hx : 0 ≤ x) : x ≤ y := by
  have := sq_le_sq.mp h; rwa [abs_of_nonneg hx, abs_of_nonneg hy] at this

theorem sum_sq_le_card_mul_max {d : ℕ} (f : Fin d → ℝ) (i0 : Fin d) (h : ∀ i, |f i| ≤ |f i0|) :
    ∑ i, f i ^ 2 ≤ d * f i0 ^ 2 := by
  calc ∑ i, f i ^ 2 ≤ ∑ _i : Fin d, f i0 ^ 2 := Finset.sum_le_sum fun i _ => sq_le_sq.2 (h i)
    _ = d * f i0 ^ 2 := by simp [Finset.sum_const, Finset.card_univ]

/-- The real arithmetic of the two-slab count: widths `ν₁ ≥ ℓa/d`, `ν₂ ≥ θℓb/d`, ratio `μ ≤ d`. -/
theorem twoSlab_real (d m : ℕ) (r θ ℓa ℓb ν₁ ν₂ μ : ℝ) (hr : 0 ≤ r) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hℓa : 0 < ℓa) (hℓb : 0 < ℓb) (hd1 : (1 : ℝ) ≤ d) (hw1 : ℓa / d ≤ ν₁) (hw2 : θ * ℓb / d ≤ ν₂)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ d) :
    ((⌊2 * r / ν₁⌋₊ + 1 : ℕ) : ℝ) * (((⌊2 * (r + μ * r) / ν₂⌋₊ + 1 : ℕ) : ℝ) * (2 * (m : ℝ) + 1) ^ (d - 2)) ≤
      twoSlabX d m r ℓa ℓb θ := by
  have hdR : (0 : ℝ) < d := by linarith
  have hν₁ : 0 < ν₁ := lt_of_lt_of_le (by positivity) hw1
  have hν₂ : 0 < ν₂ := lt_of_lt_of_le (by positivity) hw2
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * r / ν₁ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * (r + μ * r) / ν₂ := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hA1 : A ≤ 2 * r * d / ℓa := by
    rw [hA]
    calc 2 * r / ν₁ ≤ 2 * r / (ℓa / d) := div_le_div_of_nonneg_left (by positivity) (by positivity) hw1
      _ = 2 * r * d / ℓa := by field_simp
  have hB1 : B ≤ 2 * (1 + d) * r * d / (θ * ℓb) := by
    rw [hB]
    have hμr : r + μ * r ≤ (1 + d) * r := by nlinarith
    calc 2 * (r + μ * r) / ν₂ ≤ 2 * ((1 + d) * r) / ν₂ := by gcongr
      _ ≤ 2 * ((1 + d) * r) / (θ * ℓb / d) := div_le_div_of_nonneg_left (by positivity) (by positivity) hw2
      _ = 2 * (1 + d) * r * d / (θ * ℓb) := by field_simp
  have hfl : ((⌊A⌋₊ + 1 : ℕ) : ℝ) ≤ A + 1 := by push_cast; linarith [Nat.floor_le hA0]
  have hfl2 : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ B + 1 := by push_cast; linarith [Nat.floor_le hB0]
  have hm0 : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ (d - 2) := by positivity
  have step1 : ((⌊A⌋₊ + 1 : ℕ) : ℝ) * (((⌊B⌋₊ + 1 : ℕ) : ℝ) * (2 * (m : ℝ) + 1) ^ (d - 2)) ≤
      (A + 1) * ((B + 1) * (2 * (m : ℝ) + 1) ^ (d - 2)) := by
    have h0 : (0 : ℝ) ≤ ((⌊B⌋₊ + 1 : ℕ) : ℝ) := by positivity
    gcongr
  refine step1.trans ?_
  unfold twoSlabX
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hm0
  have hA2 : A ≤ 2 * r * d * (1 + d) / θ * (1 / ℓa) := by
    refine hA1.trans ?_
    have e : 2 * r * d * (1 + d) / θ * (1 / ℓa) = (2 * r * d) * ((1 + d) / θ) / ℓa := by field_simp
    rw [e]
    have : (1 : ℝ) ≤ (1 + d) / θ := by rw [le_div_iff₀ hθ0]; linarith
    have hrd : 0 ≤ 2 * r * d := by positivity
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hrd this) hℓa.le
  have hB2 : B ≤ 2 * r * d * (1 + d) / θ * (1 / ℓb) := by
    refine hB1.trans (le_of_eq ?_); field_simp
  have hAB : A * B ≤ 4 * r ^ 2 * (d : ℝ) ^ 2 * (1 + d) / (θ * ℓa * ℓb) := by
    calc A * B ≤ (2 * r * d / ℓa) * (2 * (1 + d) * r * d / (θ * ℓb)) := by gcongr
      _ = 4 * r ^ 2 * (d : ℝ) ^ 2 * (1 + d) / (θ * ℓa * ℓb) := by field_simp; ring
  have e2 : 2 * r * d * (1 + d) / θ * (1 / ℓa + 1 / ℓb) =
      2 * r * d * (1 + d) / θ * (1 / ℓa) + 2 * r * d * (1 + d) / θ * (1 / ℓb) := by ring
  rw [e2]
  nlinarith

/-- The widths of the two eliminations: a coordinate `i0` of `na` and a coordinate `i1` of the transverse part
`p = nb - (nb i0 / na i0) na`, with `|na i0| ≥ ℓa/d`, `|p i1| ≥ θℓb/d`, `|nb i0 / na i0| ≤ d`. -/
theorem twoSlab_widths (na nb : Fin d → ℤ) (θ : ℝ) (hθ0 : 0 < θ) (ℓa ℓb : ℝ) (hℓa : 0 < ℓa) (hℓb : 0 < ℓb)
    (hla : ℓa ^ 2 ≤ ∑ i, (na i : ℝ) ^ 2) (hlb : ℓb ^ 2 ≤ ∑ i, (nb i : ℝ) ^ 2)
    (hab : ∑ i, (nb i : ℝ) ^ 2 ≤ ∑ i, (na i : ℝ) ^ 2)
    (htr : θ ^ 2 * ((∑ i, (na i : ℝ) ^ 2) * ∑ i, (nb i : ℝ) ^ 2) ≤
      (∑ i, (na i : ℝ) ^ 2) * (∑ i, (nb i : ℝ) ^ 2) - (∑ i, (na i : ℝ) * (nb i : ℝ)) ^ 2) :
    (1 : ℝ) ≤ d ∧ ∃ i0 i1 : Fin d, ℓa / d ≤ |(na i0 : ℝ)| ∧
      θ * ℓb / d ≤ |(nb i1 : ℝ) - (nb i0 : ℝ) / (na i0 : ℝ) * (na i1 : ℝ)| ∧ |(nb i0 : ℝ) / (na i0 : ℝ)| ≤ d := by
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = ∑ i, (na i : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = ∑ i, (nb i : ℝ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨P, hP_def⟩ : ∃ P : ℝ, P = ∑ i, (na i : ℝ) * (nb i : ℝ) := ⟨_, rfl⟩
  rw [← ha_def] at hla hab htr
  rw [← hb_def] at hlb hab htr
  rw [← hP_def] at htr
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hla
  have hb : 0 < b := lt_of_lt_of_le (by positivity) hlb
  have hex : ∃ i, na i ≠ 0 := by
    by_contra h; push Not at h
    have : a = 0 := by rw [ha_def]; exact Finset.sum_eq_zero fun i _ => by simp [h i]
    linarith
  obtain ⟨j₀, -⟩ := hex
  have hdpos : 0 < d := Fin.pos j₀
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
  have hdR : (0 : ℝ) < d := by linarith
  refine ⟨hd1, ?_⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image univ (fun i => |(na i : ℝ)|) ⟨j₀, mem_univ _⟩
  have hmax : a ≤ d * (na i0 : ℝ) ^ 2 := by
    rw [ha_def]; exact sum_sq_le_card_mul_max (fun i => (na i : ℝ)) i0 fun i => hi0 i (mem_univ i)
  have hsq0 : 0 < (na i0 : ℝ) ^ 2 := by
    by_contra h; push Not at h; nlinarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (nb i0 : ℝ) / (na i0 : ℝ) := ⟨_, rfl⟩
  have hlam2 : lam ^ 2 ≤ (d : ℝ) ^ 2 := by
    have hnb : (nb i0 : ℝ) ^ 2 ≤ b := by
      rw [hb_def]
      exact Finset.single_le_sum (f := fun i => (nb i : ℝ) ^ 2) (fun i _ => sq_nonneg _) (mem_univ i0)
    have h1 : lam ^ 2 ≤ d := by
      rw [hlam, div_pow, div_le_iff₀ hsq0]
      nlinarith
    nlinarith
  have hlamd : |lam| ≤ d := by
    have := sq_le_sq.mp hlam2; rwa [abs_of_nonneg hdR.le] at this
  obtain ⟨p, hp⟩ : ∃ p : Fin d → ℝ, p = fun i => (nb i : ℝ) - lam * (na i : ℝ) := ⟨_, rfl⟩
  have hpe : ∑ i, p i ^ 2 = b - 2 * lam * P + lam ^ 2 * a := by
    have e : ∀ i, p i ^ 2 = (nb i : ℝ) ^ 2 - 2 * lam * ((na i : ℝ) * (nb i : ℝ)) + lam ^ 2 * (na i : ℝ) ^ 2 :=
      fun i => by rw [hp]; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ha_def, hb_def, hP_def]
  have hpsum : θ ^ 2 * b ≤ ∑ i, p i ^ 2 := by
    have h1 : a * (θ ^ 2 * b) ≤ a * ∑ i, p i ^ 2 := by
      rw [hpe]; nlinarith [sq_nonneg (lam * a - P)]
    exact le_of_mul_le_mul_left h1 ha
  obtain ⟨i1, -, hi1⟩ := Finset.exists_max_image univ (fun i => |p i|) ⟨j₀, mem_univ _⟩
  have hmax2 : ∑ i, p i ^ 2 ≤ d * p i1 ^ 2 := sum_sq_le_card_mul_max p i1 fun i => hi1 i (mem_univ i)
  refine ⟨i0, i1, ?_, ?_, by rw [← hlam]; exact hlamd⟩
  · refine le_of_sq_le_sq' (abs_nonneg _) ?_ (by positivity)
    rw [sq_abs, div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  · have e : (nb i1 : ℝ) - (nb i0 : ℝ) / (na i0 : ℝ) * (na i1 : ℝ) = p i1 := by rw [hp, hlam]
    rw [e]
    refine le_of_sq_le_sq' (abs_nonneg _) ?_ (by positivity)
    rw [sq_abs, div_pow, mul_pow, div_le_iff₀ (by positivity)]
    have h1 : θ ^ 2 * ℓb ^ 2 ≤ θ ^ 2 * b := mul_le_mul_of_nonneg_left hlb (sq_nonneg θ)
    have hdd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have h2 : (d : ℝ) * p i1 ^ 2 ≤ (d : ℝ) ^ 2 * p i1 ^ 2 := mul_le_mul_of_nonneg_right hdd (sq_nonneg _)
    linarith

/-- **Two transverse slabs, integer normals.** -/
theorem card_twoSlab_vec (S : Finset (Fin d → ℤ)) (m : ℕ) (na nb : Fin d → ℤ) (r : ℝ) (hr : 0 ≤ r)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ℓa ℓb : ℝ) (hℓa : 0 < ℓa) (hℓb : 0 < ℓb)
    (hla : ℓa ^ 2 ≤ ∑ i, (na i : ℝ) ^ 2) (hlb : ℓb ^ 2 ≤ ∑ i, (nb i : ℝ) ^ 2)
    (hab : ∑ i, (nb i : ℝ) ^ 2 ≤ ∑ i, (na i : ℝ) ^ 2)
    (htr : θ ^ 2 * ((∑ i, (na i : ℝ) ^ 2) * ∑ i, (nb i : ℝ) ^ 2) ≤
      (∑ i, (na i : ℝ) ^ 2) * (∑ i, (nb i : ℝ) ^ 2) - (∑ i, (na i : ℝ) * (nb i : ℝ)) ^ 2)
    (hS : ∀ u ∈ S, (∀ j, |u j| ≤ m) ∧ |∑ j, (na j : ℝ) * (u j : ℝ)| ≤ r ∧ |∑ j, (nb j : ℝ) * (u j : ℝ)| ≤ r) :
    (S.card : ℝ) ≤ twoSlabX d m r ℓa ℓb θ := by
  obtain ⟨hd1, i0, i1, hw1, hw2, hlam⟩ := twoSlab_widths na nb θ hθ0 ℓa ℓb hℓa hℓb hla hlb hab htr
  have hd0 : (0 : ℝ) < d := by linarith
  have hν₁ : 0 < |(na i0 : ℝ)| := lt_of_lt_of_le (by positivity) hw1
  have hν₂ : 0 < |(nb i1 : ℝ) - (nb i0 : ℝ) / (na i0 : ℝ) * (na i1 : ℝ)| := lt_of_lt_of_le (by positivity) hw2
  have hcard := card_twoSlab_gen S m (fun i => (na i : ℝ)) (fun i => (nb i : ℝ)) r r i0 i1 _ _ hν₁ le_rfl hν₂ le_rfl hS
  rw [Fintype.card_fin] at hcard
  have hcR : (S.card : ℝ) ≤ ((⌊2 * r / |(na i0 : ℝ)|⌋₊ + 1 : ℕ) : ℝ) *
      (((⌊2 * (r + |(nb i0 : ℝ) / (na i0 : ℝ)| * r) / |(nb i1 : ℝ) - (nb i0 : ℝ) / (na i0 : ℝ) * (na i1 : ℝ)|⌋₊ + 1 : ℕ) : ℝ) *
        (2 * (m : ℝ) + 1) ^ (d - 2)) := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at this ⊢
    exact this
  exact hcR.trans (twoSlab_real d m r θ ℓa ℓb _ _ _ hr hθ0 hθ1 hℓa hℓb hd1 hw1 hw2 (abs_nonneg _) hlam)

/-- **The triple count with two transverse `α`-ghost slabs** (three singleton blocks). -/
theorem card_P5_two {M : Molecule V D} (T : TriData M) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (hβ0 : ¬ T.m1.SameComponent (T.t 0) (T.f 0)) (hβ1 : ¬ T.m2.SameComponent (T.t 1) (T.f 1))
    (j₁ j₂ : Fin 3) (ρ₁ ρ₂ θ : ℝ) (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (h₁ : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ρ₁ ≤ ‖Molecule.gapAt L w κ (T.a j₁) (T.b j₁)‖)
    (h₂ : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ρ₂ ≤ ‖Molecule.gapAt L w κ (T.a j₂) (T.b j₂)‖)
    (htr : ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      θ ^ 2 * (‖Molecule.gapAt L w κ (T.a j₁) (T.b j₁)‖ ^ 2 * ‖Molecule.gapAt L w κ (T.a j₂) (T.b j₂)‖ ^ 2) ≤
        ‖Molecule.gapAt L w κ (T.a j₁) (T.b j₁)‖ ^ 2 * ‖Molecule.gapAt L w κ (T.a j₂) (T.b j₂)‖ ^ 2 -
          inner ℝ (Molecule.gapAt L w κ (T.a j₁) (T.b j₁)) (Molecule.gapAt L w κ (T.a j₂) (T.b j₂)) ^ 2) :
    (T.tripleSet L γ δ w Adm c β k0).encard ≤
      ((⌊twoSlabX d ⌊2 * L⌋₊ (2 * slabR M L γ δ) (ρ₁ * L) (ρ₂ * L) θ⌋₊ : ℕ) : ℕ∞) := by
  by_cases hne : (decSet M L γ δ w Adm c β k0).Nonempty
  swap
  · rw [T.tripleSet_empty L γ δ w Adm c β k0 hne]; simp
  obtain ⟨κs, hκs⟩ := hne
  set r : ℝ := 2 * slabR M L γ δ with hr
  have hr0 : 0 ≤ r := by rw [hr]; unfold slabR; positivity
  set n : Fin 3 → (Fin d → ℤ) := fun k => T.triZ κs k - T.triZ κs (k - 1) with hn
  have hlp : ∀ k, latticePoint L (n k) = -Molecule.gapAt L w κs (T.a k) (T.b k) := by
    intro k
    rw [gapAt_eq M T L w κs hκs.1.1 k, hn]
    simp only [latticePoint_sub]
    abel
  have hsq : ∀ k, ∑ i, (n k i : ℝ) ^ 2 = L ^ 2 * ‖Molecule.gapAt L w κs (T.a k) (T.b k)‖ ^ 2 := by
    intro k; rw [sum_sq_latticePoint L hL, hlp, norm_neg]
  have hmul : ∑ i, (n j₁ i : ℝ) * (n j₂ i : ℝ) =
      L ^ 2 * inner ℝ (Molecule.gapAt L w κs (T.a j₁) (T.b j₁)) (Molecule.gapAt L w κs (T.a j₂) (T.b j₂)) := by
    rw [sum_mul_latticePoint L hL, hlp, hlp, inner_neg_neg]
  set S : Finset (Fin d → ℤ) := (boxF d ⌊2 * L⌋₊).filter fun u =>
    |∑ i, (n j₁ i : ℝ) * (u i : ℝ)| ≤ r ∧ |∑ i, (n j₂ i : ℝ) * (u i : ℝ)| ≤ r with hS
  have hslab : ∀ κ ∈ decSet M L γ δ w Adm c β k0, ∀ k, |∑ i, (n k i : ℝ) * ((T.triZ κ 0 - T.triZ κs 0) i : ℝ)| ≤ r := by
    intro κ hκ k
    obtain ⟨hshift, hwin⟩ := T.P5_rel hβ0 hβ1 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
    have hzk : T.triZ κ k = T.triZ κs k + (T.triZ κ 0 - T.triZ κs 0) := by
      have := hshift k; funext i; have := congrFun this i
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
    have hzk1 : T.triZ κ (k - 1) = T.triZ κs (k - 1) + (T.triZ κ 0 - T.triZ κs 0) := by
      have := hshift (k - 1); funext i; have := congrFun this i
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
    have h := slab_of_energy L hL w (T.triZ κ k) (T.triZ κ (k - 1)) (T.triZ κs k) (T.triZ κs (k - 1))
      (T.triZ κ 0 - T.triZ κs 0) hzk hzk1 r (by
        have e := hwin k
        unfold triG at e
        simp only [triK] at e
        have : 2 * (r / L ^ 2) = 4 * ((M.atoms.card : ℝ) * (δ⁻¹ * L ^ (-2 * γ))) := by
          rw [hr]; unfold slabR; field_simp; ring
        rw [this]; exact e)
    exact h
  have hsub : T.tripleSet L γ δ w Adm c β k0 ⊆
      (fun u : Fin d → ℤ => fun j : Fin 3 => T.triZ κs j + u) '' (S : Set (Fin d → ℤ)) := by
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨hshift, -⟩ := T.P5_rel hβ0 hβ1 L γ δ hL hδ w Adm c β k0 κ κs hκ hκs
    refine ⟨T.triZ κ 0 - T.triZ κs 0, ?_, ?_⟩
    · rw [Finset.mem_coe, hS, Finset.mem_filter]
      exact ⟨T.box_u L γ δ hL w Adm c β k0 κ κs hκ hκs 0, hslab κ hκ j₁, hslab κ hκ j₂⟩
    · funext j
      have := hshift j
      show T.triZ κs j + (T.triZ κ 0 - T.triZ κs 0) = T.triZ κ j
      funext i; have := congrFun this i
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢; omega
  have hmemS : ∀ u ∈ S, (∀ i, |u i| ≤ (⌊2 * L⌋₊ : ℤ)) ∧ |∑ i, (n j₁ i : ℝ) * (u i : ℝ)| ≤ r ∧
      |∑ i, (n j₂ i : ℝ) * (u i : ℝ)| ≤ r := by
    intro u hu
    rw [hS, Finset.mem_filter, mem_boxF] at hu
    exact ⟨hu.1, hu.2.1, hu.2.2⟩
  -- the transversality and the lower bounds in integer form
  have hg1 := h₁ κs hκs
  have hg2 := h₂ κs hκs
  have htr0 := htr κs hκs
  have hL2 : 0 < L ^ 2 := by positivity
  have hl1 : (ρ₁ * L) ^ 2 ≤ ∑ i, (n j₁ i : ℝ) ^ 2 := by
    rw [hsq, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ₁.le hg1 2) hL2.le
  have hl2 : (ρ₂ * L) ^ 2 ≤ ∑ i, (n j₂ i : ℝ) ^ 2 := by
    rw [hsq, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ₂.le hg2 2) hL2.le
  have htrZ : θ ^ 2 * ((∑ i, (n j₁ i : ℝ) ^ 2) * ∑ i, (n j₂ i : ℝ) ^ 2) ≤
      (∑ i, (n j₁ i : ℝ) ^ 2) * (∑ i, (n j₂ i : ℝ) ^ 2) - (∑ i, (n j₁ i : ℝ) * (n j₂ i : ℝ)) ^ 2 := by
    rw [hsq, hsq, hmul]
    have hL4 : 0 ≤ (L ^ 2) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left htr0 hL4
    nlinarith
  have hcardR : (S.card : ℝ) ≤ twoSlabX d ⌊2 * L⌋₊ r (ρ₁ * L) (ρ₂ * L) θ := by
    rcases le_total (∑ i, (n j₂ i : ℝ) ^ 2) (∑ i, (n j₁ i : ℝ) ^ 2) with hab | hab
    · exact card_twoSlab_vec S ⌊2 * L⌋₊ (n j₁) (n j₂) r hr0 θ hθ0 hθ1 (ρ₁ * L) (ρ₂ * L) (by positivity)
        (by positivity) hl1 hl2 hab htrZ (fun u hu => by
          obtain ⟨h1, h2, h3⟩ := hmemS u hu; exact ⟨h1, h2, h3⟩)
    · rw [twoSlabX_comm]
      refine card_twoSlab_vec S ⌊2 * L⌋₊ (n j₂) (n j₁) r hr0 θ hθ0 hθ1 (ρ₂ * L) (ρ₁ * L) (by positivity)
        (by positivity) hl2 hl1 hab ?_ (fun u hu => by
          obtain ⟨h1, h2, h3⟩ := hmemS u hu; exact ⟨h1, h3, h2⟩)
      have e : (∑ i, (n j₂ i : ℝ) * (n j₁ i : ℝ)) = ∑ i, (n j₁ i : ℝ) * (n j₂ i : ℝ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [e]; nlinarith
  have h1 := encard_le_of_subset_image _ _ _ hsub
  refine h1.trans ?_
  exact_mod_cast Nat.le_floor hcardR

end WaveTurbulence.GammaLow.FinalCount.Ghost
