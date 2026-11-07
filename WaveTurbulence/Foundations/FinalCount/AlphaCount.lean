/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AlphaCover2
/-! The `α`-cut (FINALCOUNT-G2 step 4), part 4: the count and the explicit deviation. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem card_alphaN_le (L : ℝ) (r₀ : Mom d) (ρ : ℝ) (hL : 0 < L) (hρ : 0 ≤ ρ) :
    (alphaN d L r₀ ρ).card ≤ (⌊2 * ρ * L⌋₊ + 1) ^ d := by
  unfold alphaN
  rw [Fintype.card_piFinset]
  simp only [Finset.card_univ, Fintype.card_fin]
  calc ∏ i : Fin d, (Finset.Icc ⌈L * r₀ i - ρ * L⌉ ⌊L * r₀ i + ρ * L⌋).card
      ≤ ∏ _i : Fin d, (⌊2 * ρ * L⌋₊ + 1) := by
        refine Finset.prod_le_prod' fun i _ => ?_
        rw [Int.card_Icc]
        have h1 := Int.floor_le (L * r₀ i + ρ * L)
        have h2 := Int.le_ceil (L * r₀ i - ρ * L)
        have h3 : (⌊L * r₀ i + ρ * L⌋ - ⌈L * r₀ i - ρ * L⌉ : ℤ) ≤ ⌊2 * ρ * L⌋ :=
          Int.le_floor.mpr (by push_cast; linarith)
        have h4 := Int.natCast_floor_eq_floor (a := 2 * ρ * L) (by positivity)
        omega
    _ = (⌊2 * ρ * L⌋₊ + 1) ^ d := by simp

theorem card_alphaJ_le (L τ R : ℝ) (hτ : 0 < τ) (hR : 0 ≤ R) (s₀ : Mom d) (n : Fin d → ℤ) :
    ((alphaJ L τ R s₀ n).card : ℝ) ≤ 8 * R / τ + 4 := by
  unfold alphaJ
  rw [Int.card_Icc]
  set a := alphaCenter L τ s₀ n - (1 / 2 + 4 * R / τ)
  set b := alphaCenter L τ s₀ n + (1 / 2 + 4 * R / τ)
  have h1 : (a - 1 : ℝ) < ⌊a⌋ := Int.sub_one_lt_floor a
  have h2 : (⌈b⌉ : ℝ) < b + 1 := Int.ceil_lt_add_one b
  have hba : b - a = 1 + 8 * R / τ := by simp only [a, b]; ring
  have : ((⌈b⌉ + 1 - ⌊a⌋ : ℤ) : ℝ) ≤ 8 * R / τ + 4 := by
    push_cast; linarith
  by_cases hnn : 0 ≤ ⌈b⌉ + 1 - ⌊a⌋
  · rw [← Int.toNat_of_nonneg hnn] at this
    exact_mod_cast this
  · push Not at hnn
    rw [Int.toNat_of_nonpos hnn.le]
    simp only [Nat.cast_zero]
    positivity

/-- The number of post classes. -/
noncomputable def alphaN' (d : ℕ) (L τ R ρ : ℝ) : ℕ :=
  (⌊2 * ρ * L⌋₊ + 1) ^ d * (2 * (⌈8 * R / τ⌉₊ + 4))

theorem card_alphaIndex_le (L τ R : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hR : 0 ≤ R) (s₀ r₀ : Mom d) (ρ : ℝ)
    (hρ : 0 ≤ ρ) : (alphaIndex d L τ R s₀ r₀ ρ).card ≤ alphaN' d L τ R ρ := by
  unfold alphaIndex
  refine (Finset.card_biUnion_le).trans ?_
  have hJ : ∀ n, (alphaJ L τ R s₀ n).card ≤ ⌈8 * R / τ⌉₊ + 4 := by
    intro n
    have := card_alphaJ_le L τ R hτ hR s₀ n
    have h2 : 8 * R / τ ≤ ⌈8 * R / τ⌉₊ := Nat.le_ceil _
    have : ((alphaJ L τ R s₀ n).card : ℝ) ≤ ((⌈8 * R / τ⌉₊ + 4 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  calc ∑ n ∈ alphaN d L r₀ ρ, (((alphaJ L τ R s₀ n) ×ˢ ({-1, 1} : Finset ℤ)).image (fun p => (n, p.1, p.2))).card
      ≤ ∑ n ∈ alphaN d L r₀ ρ, (2 * (⌈8 * R / τ⌉₊ + 4)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_product, Finset.card_pair (by norm_num : (-1 : ℤ) ≠ 1)]
        have := hJ n
        omega
    _ ≤ alphaN' d L τ R ρ := by
        rw [Finset.sum_const, smul_eq_mul]
        unfold alphaN'
        exact Nat.mul_le_mul_right _ (card_alphaN_le L r₀ ρ hL hρ)

theorem alphaN'_le (L τ R ρ : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hR : 0 ≤ R) (hρ : 0 ≤ ρ) :
    (alphaN' d L τ R ρ : ℝ) ≤ (2 * ρ * L + 1) ^ d * (2 * (8 * R / τ + 5)) := by
  unfold alphaN'
  push_cast
  have h1 : (⌊2 * ρ * L⌋₊ : ℝ) ≤ 2 * ρ * L := Nat.floor_le (by positivity)
  have h2 : (⌈8 * R / τ⌉₊ : ℝ) < 8 * R / τ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hpos : (0 : ℝ) ≤ (⌊2 * ρ * L⌋₊ : ℝ) + 1 := by positivity
  exact mul_le_mul (pow_le_pow_left₀ hpos (by linarith) d) (by linarith) (by positivity) (by positivity)

/-- **α-cut count.** The gap lies in the ball `‖gap - r₀‖ ≤ ρ`, with `r₀` determined by the parameters. -/
theorem countE_le_alpha_cut (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (L γ δ : ℝ) (hδ : 0 < δ) (hL : 0 < L) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (R ρ : ℝ) (hR : 0 ≤ R)
    (hρ : 0 ≤ ρ) (hgap : ∀ κ, Adm κ → ‖Molecule.gapAt L w κ x₁ x₂‖ ≤ 2 * R)
    (hball : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ x₁ x₂ - r₀‖ ≤ ρ) :
    M.countE L γ δ w Adm ≤
      ((alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R ρ : ℕ) : ℕ∞) * (M.cut v v₂ x₁ x₂).countE L γ δ w Adm := by
  have hτ : 0 < δ⁻¹ * L ^ (-2 * γ) := by positivity
  refine countE_le_mul_of_cover M (M.cut v v₂ x₁ x₂) L γ δ w Adm Adm _ ?_
  intro c β k0 hP
  obtain ⟨r₀, hr₀⟩ := hball c β k0 hP
  refine ⟨(Fin d → ℤ) × ℤ × ℤ, alphaIndex d L (δ⁻¹ * L ^ (-2 * γ)) R (k0 x₁ + k0 x₂) r₀ ρ,
    fun i => alphaParams v v₂ L (δ⁻¹ * L ^ (-2 * γ)) c β k0 i.1 i.2.1 i.2.2, ?_, ?_, ?_⟩
  · exact card_alphaIndex_le L _ R hL hτ hR _ _ ρ hρ
  · intro i _
    exact alpha_paramOK M hcd hdeg _ _ c β k0 hP i.1 i.2.1 i.2.2
  · exact alpha_cover M hcd L γ δ hδ hL w Adm R hgap c β k0 r₀ ρ hr₀

end WaveTurbulence.FinalCount
