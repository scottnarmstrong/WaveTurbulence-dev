/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RungKinds
/-! # Weight kinds and their closure under products (S3b LADDER-DECAY)

A rung weight is `ι(p) * cutW`, with `ι` of one of four kinds: constant `1`, a function of the first
variable supported in a short cube, a function of the second variable supported in a short cube,
or a function supported in a finite set of bounded cardinality. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset

variable {d : ℕ}

/-- Integer points of a cube. -/
def InCube (q : Fin d → ℝ) (R : ℝ) (x : Fin d → ℤ) : Prop := ∀ i, |(x i : ℝ) - q i| ≤ R

/-- The finite interval box of a cube. -/
noncomputable def cubeI (q : Fin d → ℝ) (R : ℝ) : Fin d → Finset ℤ :=
  fun i => Finset.Icc ⌈q i - R⌉ ⌊q i + R⌋

lemma mem_cubeI {q : Fin d → ℝ} {R : ℝ} {x : Fin d → ℤ} (hx : InCube q R x) :
    x ∈ Fintype.piFinset (cubeI q R) := by
  rw [Fintype.mem_piFinset]
  intro i
  have h := abs_le.mp (hx i)
  rw [cubeI, Finset.mem_Icc]
  exact ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩

lemma cubeI_diam {q : Fin d → ℝ} {R : ℝ} (hR : 0 ≤ R) (i : Fin d) :
    ∀ n ∈ cubeI q R i, ∀ n' ∈ cubeI q R i, |(n : ℝ) - n'| ≤ 2 * R + 1 := by
  intro n hn n' hn'
  simp only [cubeI, Finset.mem_Icc] at hn hn'
  have h1 : (n : ℝ) ≤ q i + R := by
    have := hn.2; exact_mod_cast (Int.le_floor.mp this)
  have h2 : q i - R ≤ (n : ℝ) := by
    have := hn.1; exact_mod_cast (Int.ceil_le.mp this)
  have h3 : (n' : ℝ) ≤ q i + R := by
    have := hn'.2; exact_mod_cast (Int.le_floor.mp this)
  have h4 : q i - R ≤ (n' : ℝ) := by
    have := hn'.1; exact_mod_cast (Int.ceil_le.mp this)
  rw [abs_le]; constructor <;> linarith

lemma cubeI_card {q : Fin d → ℝ} {R : ℝ} (hR : 0 ≤ R) (i : Fin d) :
    ((cubeI q R i).card : ℝ) ≤ 2 * R + 1 := by
  simp only [cubeI, Int.card_Icc]
  have h1 := Int.floor_le (q i + R)
  have h2 := Int.le_ceil (q i - R)
  have h3 : (⌊q i + R⌋ + 1 - ⌈q i - R⌉ : ℤ) ≤ ⌊q i + R⌋ + 1 - ⌈q i - R⌉ := le_rfl
  by_cases h : ⌈q i - R⌉ ≤ ⌊q i + R⌋ + 1
  · have : ((⌊q i + R⌋ + 1 - ⌈q i - R⌉).toNat : ℝ) = ((⌊q i + R⌋ + 1 - ⌈q i - R⌉ : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ ⌊q i + R⌋ + 1 - ⌈q i - R⌉ := by omega
      exact_mod_cast Int.toNat_of_nonneg this
    rw [this]
    push_cast
    linarith
  · have : (⌊q i + R⌋ + 1 - ⌈q i - R⌉).toNat = 0 := by omega
    rw [this]; simp; linarith

/-- Kind `X`: a function of the first variable supported in a cube of radius `R`. -/
def KindX (R : ℝ) (ι : Pt d → ℝ) : Prop :=
  ∃ (q : Fin d → ℝ) (f : (Fin d → ℤ) → ℝ), (∀ x, |f x| ≤ 1) ∧ (∀ x, f x ≠ 0 → InCube q R x) ∧
    ∀ p, ι p = f p.1

/-- Kind `Y`. -/
def KindY (R : ℝ) (ι : Pt d → ℝ) : Prop :=
  ∃ (q : Fin d → ℝ) (f : (Fin d → ℤ) → ℝ), (∀ x, |f x| ≤ 1) ∧ (∀ x, f x ≠ 0 → InCube q R x) ∧
    ∀ p, ι p = f p.2

/-- Kind `Z`: bounded and supported in a finite set of at most `N` points. -/
def KindZ (N : ℝ) (ι : Pt d → ℝ) : Prop :=
  (∀ p, |ι p| ≤ 1) ∧ ∃ T : Finset (Pt d), (T.card : ℝ) ≤ N ∧ ∀ p, ι p ≠ 0 → p ∈ T

lemma KindX.mul {R : ℝ} {ι₁ ι₂ : Pt d → ℝ} (h₁ : KindX R ι₁) (h₂ : KindX R ι₂) :
    KindX R (fun p => ι₁ p * ι₂ p) := by
  obtain ⟨q₁, f₁, hf₁, hs₁, he₁⟩ := h₁
  obtain ⟨q₂, f₂, hf₂, hs₂, he₂⟩ := h₂
  refine ⟨q₁, fun x => f₁ x * f₂ x, fun x => ?_, fun x hx => ?_, fun p => ?_⟩
  · rw [abs_mul]; exact mul_le_one₀ (hf₁ x) (abs_nonneg _) (hf₂ x)
  · exact hs₁ x (left_ne_zero_of_mul hx)
  · simp only [he₁, he₂]

lemma KindY.mul {R : ℝ} {ι₁ ι₂ : Pt d → ℝ} (h₁ : KindY R ι₁) (h₂ : KindY R ι₂) :
    KindY R (fun p => ι₁ p * ι₂ p) := by
  obtain ⟨q₁, f₁, hf₁, hs₁, he₁⟩ := h₁
  obtain ⟨q₂, f₂, hf₂, hs₂, he₂⟩ := h₂
  refine ⟨q₁, fun x => f₁ x * f₂ x, fun x => ?_, fun x hx => ?_, fun p => ?_⟩
  · rw [abs_mul]; exact mul_le_one₀ (hf₁ x) (abs_nonneg _) (hf₂ x)
  · exact hs₁ x (left_ne_zero_of_mul hx)
  · simp only [he₁, he₂]

lemma KindX.abs_le {R : ℝ} {ι : Pt d → ℝ} (h : KindX R ι) : ∀ p, |ι p| ≤ 1 := by
  obtain ⟨q, f, hf, _, he⟩ := h
  intro p; rw [he]; exact hf _

lemma KindY.abs_le {R : ℝ} {ι : Pt d → ℝ} (h : KindY R ι) : ∀ p, |ι p| ≤ 1 := by
  obtain ⟨q, f, hf, _, he⟩ := h
  intro p; rw [he]; exact hf _

/-- A product of an `X` and a `Y` function is supported in a product of two cubes. -/
lemma KindX.mul_Y {R : ℝ} (hR : 0 ≤ R) {ι₁ ι₂ : Pt d → ℝ} (h₁ : KindX R ι₁) (h₂ : KindY R ι₂) :
    KindZ ((2 * R + 1) ^ d * (2 * R + 1) ^ d) (fun p => ι₁ p * ι₂ p) := by
  obtain ⟨q₁, f₁, hf₁, hs₁, he₁⟩ := h₁
  obtain ⟨q₂, f₂, hf₂, hs₂, he₂⟩ := h₂
  refine ⟨fun p => ?_, Fintype.piFinset (cubeI q₁ R) ×ˢ Fintype.piFinset (cubeI q₂ R), ?_, ?_⟩
  · rw [abs_mul, he₁, he₂]; exact mul_le_one₀ (hf₁ _) (abs_nonneg _) (hf₂ _)
  · rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset]
    push_cast
    have h1 : ∏ i : Fin d, ((cubeI q₁ R i).card : ℝ) ≤ ∏ _i : Fin d, (2 * R + 1) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => cubeI_card hR i)
    have h2 : ∏ i : Fin d, ((cubeI q₂ R i).card : ℝ) ≤ ∏ _i : Fin d, (2 * R + 1) :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => cubeI_card hR i)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1 h2
    exact mul_le_mul h1 h2 (Finset.prod_nonneg (fun _ _ => Nat.cast_nonneg _)) (by positivity)
  · intro p hp
    rw [Finset.mem_product]
    refine ⟨mem_cubeI (hs₁ _ ?_), mem_cubeI (hs₂ _ ?_)⟩
    · have hp' : ι₁ p * ι₂ p ≠ 0 := hp
      have := left_ne_zero_of_mul hp'
      rwa [he₁] at this
    · have hp' : ι₁ p * ι₂ p ≠ 0 := hp
      have := right_ne_zero_of_mul hp'
      rwa [he₂] at this

end WaveTurbulence.LadderDecay
