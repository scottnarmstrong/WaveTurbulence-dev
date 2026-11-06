/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ChainBound
public import WaveTurbulence.Foundations.Spine.EpsIE
/-! # Equality and ball indicators of the slot-difference forms (S3b LADDER-DECAY)

Indicators of `m p + c = 0` and `‖φ(m p + c)‖ ≤ ρ` for a rung point `p = (x, y)` and a form `m`
that is an axis form (`±x`, `±y`) or a diagonal form (`±x ± y`) are good rung terms, and products
of good terms are good terms. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset WaveTurbulence WaveTurbulence.WeylSums

variable {d : ℕ}

/-- Indicator of `m p + c = 0`. -/
def eqInd (m : Pt d →+ (Fin d → ℤ)) (c : Fin d → ℤ) (p : Pt d) : ℝ :=
  if m p + c = 0 then 1 else 0

/-- Indicator of `‖φ(m p + c)‖ ≤ ρ`. -/
noncomputable def ballInd (L ρ : ℝ) (m : Pt d →+ (Fin d → ℤ)) (c : Fin d → ℤ) (p : Pt d) : ℝ :=
  if ‖latticePoint L (m p + c)‖ ≤ ρ then 1 else 0

def AxisX (m : Pt d →+ (Fin d → ℤ)) : Prop := (∀ p, m p = p.1) ∨ (∀ p, m p = -p.1)
def AxisY (m : Pt d →+ (Fin d → ℤ)) : Prop := (∀ p, m p = p.2) ∨ (∀ p, m p = -p.2)
def DiagF (m : Pt d →+ (Fin d → ℤ)) : Prop :=
  ∃ s t : ℤ, (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧ ∀ p, m p = s • p.1 + t • p.2

lemma eqInd_abs_le (m : Pt d →+ (Fin d → ℤ)) (c : Fin d → ℤ) (p : Pt d) : |eqInd m c p| ≤ 1 := by
  unfold eqInd; split_ifs <;> simp

lemma ballInd_abs_le (L ρ : ℝ) (m : Pt d →+ (Fin d → ℤ)) (c : Fin d → ℤ) (p : Pt d) :
    |ballInd L ρ m c p| ≤ 1 := by
  unfold ballInd; split_ifs <;> simp

lemma goodTerm_one (L R : ℝ) (a b : Fin d → ℝ) : GoodTerm L R a b (fun _ => (1 : ℝ)) :=
  Or.inl (fun _ => rfl)

lemma eqInd_goodX {L R : ℝ} {a b : Fin d → ℝ} {m : Pt d →+ (Fin d → ℤ)} (hm : AxisX m) (c : Fin d → ℤ)
    (hR : 0 ≤ R) : GoodTerm L R a b (eqInd m c) := by
  refine Or.inr (Or.inl ?_)
  rcases hm with hm | hm
  · refine ⟨fun j => -(c j : ℝ), fun x => if x + c = 0 then 1 else 0, fun x => ?_, fun x hx j => ?_,
      fun p => ?_⟩
    · dsimp only; split_ifs <;> simp
    · have h : x + c = 0 := by by_contra h; exact hx (by simp [h])
      have : x j = - c j := by have := congrFun h j; simp at this; linarith
      simp [this, hR]
    · simp [eqInd, hm p]
  · refine ⟨fun j => (c j : ℝ), fun x => if -x + c = 0 then 1 else 0, fun x => ?_, fun x hx j => ?_,
      fun p => ?_⟩
    · dsimp only; split_ifs <;> simp
    · have h : -x + c = 0 := by by_contra h; exact hx (by simp [h])
      have : x j = c j := by have := congrFun h j; simp at this; linarith
      simp [this, hR]
    · simp [eqInd, hm p]

lemma eqInd_goodY {L R : ℝ} {a b : Fin d → ℝ} {m : Pt d →+ (Fin d → ℤ)} (hm : AxisY m) (c : Fin d → ℤ)
    (hR : 0 ≤ R) : GoodTerm L R a b (eqInd m c) := by
  refine Or.inr (Or.inr (Or.inl ?_))
  rcases hm with hm | hm
  · refine ⟨fun j => -(c j : ℝ), fun x => if x + c = 0 then 1 else 0, fun x => ?_, fun x hx j => ?_,
      fun p => ?_⟩
    · dsimp only; split_ifs <;> simp
    · have h : x + c = 0 := by by_contra h; exact hx (by simp [h])
      have : x j = - c j := by have := congrFun h j; simp at this; linarith
      simp [this, hR]
    · simp [eqInd, hm p]
  · refine ⟨fun j => (c j : ℝ), fun x => if -x + c = 0 then 1 else 0, fun x => ?_, fun x hx j => ?_,
      fun p => ?_⟩
    · dsimp only; split_ifs <;> simp
    · have h : -x + c = 0 := by by_contra h; exact hx (by simp [h])
      have : x j = c j := by have := congrFun h j; simp at this; linarith
      simp [this, hR]
    · simp [eqInd, hm p]

lemma eqInd_goodDiag {L R : ℝ} {a b : Fin d → ℝ} {m : Pt d →+ (Fin d → ℤ)} (hm : DiagF m)
    (c : Fin d → ℤ) (hL : 0 < L) : GoodTerm L R a b (eqInd m c) := by
  obtain ⟨s, t, hs, ht, hm⟩ := hm
  refine Or.inr (Or.inr (Or.inr ⟨eqInd_abs_le m c, ?_⟩))
  refine ⟨(Counting.latticeBox (fun j => L * a j) (4 * L)).image
    (fun x => (x, -(t • (s • x + c)))), ?_, ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    have h1 := Counting.card_latticeBox_le (fun j => L * a j) (L := 4 * L) (by linarith)
    have h2 : (2 * (4 * L) + 1) = 8 * L + 1 := by ring
    rw [h2] at h1
    have h3 : 0 ≤ (2 * R + 1) ^ (2 * d) := by
      rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
    exact h1.trans (by linarith)
  · intro p hp
    have h1 : eqInd m c p ≠ 0 := by
      intro h0; apply hp; rw [h0]; simp
    have h2 : cutW L a b p ≠ 0 := right_ne_zero_of_mul hp
    have hmp : m p + c = 0 := by by_contra h; exact h1 (by simp [eqInd, h])
    have hx := (cutW_ne_zero_x hL a b p h2).1
    refine Finset.mem_image.mpr ⟨p.1, hx, ?_⟩
    have e1 : s • p.1 + t • p.2 + c = 0 := by rw [← hm p]; exact hmp
    have e2 : t • (t • p.2) = p.2 := by
      rcases ht with rfl | rfl <;> simp
    have e3 : t • p.2 = -(s • p.1 + c) := by
      refine eq_neg_of_add_eq_zero_left ?_
      rw [← e1]; abel
    refine Prod.ext rfl ?_
    simp only
    have e4 : s • p.1 + c = -(t • p.2) := by rw [e3]; simp
    rw [e4, smul_neg, e2]; simp

lemma latticePoint_apply' (L : ℝ) (v : Fin d → ℤ) (j : Fin d) : (latticePoint L v) j = (v j : ℝ) / L := rfl

lemma coord_le_of_ball {L ρ : ℝ} (hL : 0 < L) {v : Fin d → ℤ} (h : ‖latticePoint L v‖ ≤ ρ) (j : Fin d) :
    |(v j : ℝ)| ≤ L * ρ := by
  have h1 : ‖(latticePoint L v) j‖ ≤ ‖latticePoint L v‖ := PiLp.norm_apply_le _ j
  rw [Real.norm_eq_abs, latticePoint_apply', abs_div, abs_of_pos hL, div_le_iff₀ hL] at h1
  nlinarith

lemma ballInd_goodX {L ρ R : ℝ} {a b : Fin d → ℝ} {m : Pt d →+ (Fin d → ℤ)} (hm : AxisX m)
    (c : Fin d → ℤ) (hL : 0 < L) (hR : L * ρ ≤ R) : GoodTerm L R a b (ballInd L ρ m c) := by
  refine Or.inr (Or.inl ?_)
  rcases hm with hm | hm
  · refine ⟨fun j => -(c j : ℝ), fun x => if ‖latticePoint L (x + c)‖ ≤ ρ then 1 else 0,
      fun x => ?_, fun x hx j => ?_, fun p => ?_⟩
    · dsimp only; split_ifs <;> simp
    · have h : ‖latticePoint L (x + c)‖ ≤ ρ := by by_contra h; exact hx (by simp [h])
      have := coord_le_of_ball hL h j
      simp only [Pi.add_apply, Int.cast_add] at this
      have e : (x j : ℝ) - -(c j : ℝ) = (x j : ℝ) + c j := by ring
      rw [e]; exact this.trans hR
    · simp [ballInd, hm p]
  · refine ⟨fun j => (c j : ℝ), fun x => if ‖latticePoint L (-x + c)‖ ≤ ρ then 1 else 0,
      fun x => ?_, fun x hx j => ?_, fun p => ?_⟩
    · dsimp only; split_ifs <;> simp
    · have h : ‖latticePoint L (-x + c)‖ ≤ ρ := by by_contra h; exact hx (by simp [h])
      have := coord_le_of_ball hL h j
      simp only [Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg] at this
      have e : |(x j : ℝ) - c j| = |-(x j : ℝ) + c j| := by rw [← abs_neg]; ring_nf
      rw [e]; exact this.trans hR
    · simp [ballInd, hm p]

lemma ballInd_goodY {L ρ R : ℝ} {a b : Fin d → ℝ} {m : Pt d →+ (Fin d → ℤ)} (hm : AxisY m)
    (c : Fin d → ℤ) (hL : 0 < L) (hR : L * ρ ≤ R) : GoodTerm L R a b (ballInd L ρ m c) := by
  refine Or.inr (Or.inr (Or.inl ?_))
  rcases hm with hm | hm
  · refine ⟨fun j => -(c j : ℝ), fun x => if ‖latticePoint L (x + c)‖ ≤ ρ then 1 else 0,
      fun x => ?_, fun x hx j => ?_, fun p => ?_⟩
    · dsimp only; split_ifs <;> simp
    · have h : ‖latticePoint L (x + c)‖ ≤ ρ := by by_contra h; exact hx (by simp [h])
      have := coord_le_of_ball hL h j
      simp only [Pi.add_apply, Int.cast_add] at this
      have e : (x j : ℝ) - -(c j : ℝ) = (x j : ℝ) + c j := by ring
      rw [e]; exact this.trans hR
    · simp [ballInd, hm p]
  · refine ⟨fun j => (c j : ℝ), fun x => if ‖latticePoint L (-x + c)‖ ≤ ρ then 1 else 0,
      fun x => ?_, fun x hx j => ?_, fun p => ?_⟩
    · dsimp only; split_ifs <;> simp
    · have h : ‖latticePoint L (-x + c)‖ ≤ ρ := by by_contra h; exact hx (by simp [h])
      have := coord_le_of_ball hL h j
      simp only [Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg] at this
      have e : |(x j : ℝ) - c j| = |-(x j : ℝ) + c j| := by rw [← abs_neg]; ring_nf
      rw [e]; exact this.trans hR
    · simp [ballInd, hm p]

/-- The finite-set kind. -/
def ZLike (L R : ℝ) (a b : Fin d → ℝ) (χ : Pt d → ℝ) : Prop :=
  (∀ p, |χ p| ≤ 1) ∧ ∃ T : Finset (Pt d),
    (T.card : ℝ) ≤ (2 * R + 1) ^ (2 * d) + (8 * L + 1) ^ d ∧
    ∀ p, ((χ p : ℝ) : ℂ) * cutW L a b p ≠ 0 → p ∈ T

lemma ZLike.mul_left {L R : ℝ} {a b : Fin d → ℝ} {χ₁ χ₂ : Pt d → ℝ} (h : ZLike L R a b χ₁)
    (h2 : ∀ p, |χ₂ p| ≤ 1) : ZLike L R a b (fun p => χ₁ p * χ₂ p) := by
  obtain ⟨hb, T, hT, hs⟩ := h
  refine ⟨fun p => ?_, T, hT, fun p hp => hs p ?_⟩
  · rw [abs_mul]; exact mul_le_one₀ (hb p) (abs_nonneg _) (h2 p)
  · intro h0; apply hp
    have : ((χ₁ p : ℝ) : ℂ) * cutW L a b p = 0 := h0
    push_cast
    rw [mul_assoc, mul_comm ((χ₂ p : ℂ)), ← mul_assoc, this]; simp

lemma ZLike.mul_right {L R : ℝ} {a b : Fin d → ℝ} {χ₁ χ₂ : Pt d → ℝ} (h : ZLike L R a b χ₂)
    (h1 : ∀ p, |χ₁ p| ≤ 1) : ZLike L R a b (fun p => χ₁ p * χ₂ p) := by
  have := h.mul_left h1
  have e : (fun p => χ₁ p * χ₂ p) = (fun p => χ₂ p * χ₁ p) := by funext p; ring
  rw [e]; exact this

lemma GoodTerm.mul {L R : ℝ} {a b : Fin d → ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) {χ₁ χ₂ : Pt d → ℝ}
    (h1 : GoodTerm L R a b χ₁) (h2 : GoodTerm L R a b χ₂) :
    GoodTerm L R a b (fun p => χ₁ p * χ₂ p) := by
  have a1 := h1.abs_le
  have a2 := h2.abs_le
  have hX : ∀ {χ : Pt d → ℝ}, ZLike L R a b χ → GoodTerm L R a b χ := fun h => Or.inr (Or.inr (Or.inr h))
  have XY : ∀ {χ₁ χ₂ : Pt d → ℝ}, KindX R χ₁ → KindY R χ₂ →
      GoodTerm L R a b (fun p => χ₁ p * χ₂ p) := by
    intro χ₁ χ₂ hx hy
    obtain ⟨hb, T, hT, hs⟩ := KindX.mul_Y hR hx hy
    refine hX ⟨hb, T, hT.trans (by
      have : 0 ≤ (8 * L + 1) ^ d := pow_nonneg (by linarith) _
      have e : (2 * R + 1) ^ d * (2 * R + 1) ^ d = (2 * R + 1) ^ (2 * d) := by
        rw [← pow_add]; ring_nf
      rw [e]; linarith), fun p hp => hs p ?_⟩
    intro h0; apply hp; simp [h0]
  rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2
  · left; intro p; simp [h1 p, h2 p]
  · have : (fun p => χ₁ p * χ₂ p) = χ₂ := by funext p; simp [h1 p]
    rw [this]; exact Or.inr (Or.inl h2)
  · have : (fun p => χ₁ p * χ₂ p) = χ₂ := by funext p; simp [h1 p]
    rw [this]; exact Or.inr (Or.inr (Or.inl h2))
  · have : (fun p => χ₁ p * χ₂ p) = χ₂ := by funext p; simp [h1 p]
    rw [this]; exact Or.inr (Or.inr (Or.inr h2))
  · have : (fun p => χ₁ p * χ₂ p) = χ₁ := by funext p; simp [h2 p]
    rw [this]; exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inl (h1.mul h2))
  · exact XY h1 h2
  · exact hX (ZLike.mul_right h2 (KindX.abs_le h1))
  · have : (fun p => χ₁ p * χ₂ p) = χ₁ := by funext p; simp [h2 p]
    rw [this]; exact Or.inr (Or.inr (Or.inl h1))
  · have e : (fun p => χ₁ p * χ₂ p) = (fun p => χ₂ p * χ₁ p) := by funext p; ring
    rw [e]; exact XY h2 h1
  · exact Or.inr (Or.inr (Or.inl (h1.mul h2)))
  · exact hX (ZLike.mul_right h2 (KindY.abs_le h1))
  · have : (fun p => χ₁ p * χ₂ p) = χ₁ := by funext p; simp [h2 p]
    rw [this]; exact Or.inr (Or.inr (Or.inr h1))
  · exact hX (ZLike.mul_left h1 (KindX.abs_le h2))
  · exact hX (ZLike.mul_left h1 (KindY.abs_le h2))
  · exact hX (ZLike.mul_left h1 a2)

/-- A signed sum of good terms. -/
def GoodSum (L R : ℝ) (a b : Fin d → ℝ) (J : Type) [Fintype J] (w : Pt d → ℝ) : Prop :=
  ∃ (s : J → ℝ) (χ : J → Pt d → ℝ), (∀ j, |s j| ≤ 1) ∧ (∀ j, GoodTerm L R a b (χ j)) ∧
    ∀ p, w p = ∑ j, s j * χ j p

lemma GoodSum.mul {L R : ℝ} {a b : Fin d → ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
    {w₁ w₂ : Pt d → ℝ} (h1 : GoodSum L R a b J₁ w₁) (h2 : GoodSum L R a b J₂ w₂) :
    GoodSum L R a b (J₁ × J₂) (fun p => w₁ p * w₂ p) := by
  obtain ⟨s₁, χ₁, hs₁, hχ₁, he₁⟩ := h1
  obtain ⟨s₂, χ₂, hs₂, hχ₂, he₂⟩ := h2
  refine ⟨fun j => s₁ j.1 * s₂ j.2, fun j p => χ₁ j.1 p * χ₂ j.2 p, fun j => ?_,
    fun j => GoodTerm.mul hL hR (hχ₁ j.1) (hχ₂ j.2), fun p => ?_⟩
  · rw [abs_mul]; exact mul_le_one₀ (hs₁ _) (abs_nonneg _) (hs₂ _)
  · dsimp only
    rw [he₁ p, he₂ p, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

end WaveTurbulence.LadderDecay
