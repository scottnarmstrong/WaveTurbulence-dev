/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepMom2

/-! # U1 UCLK-MOM: `ModesMomentSel`

Main's `Represents.tsum_modes_moment` with per-slot time weights `θ s` and the residual-selection moment
`⟨ω^{nr}⟩^{1/18}` at the slots of `sel` (U-clock (U.4)). The constant is `27 = 3^3` (each slot: `3^{2c+e} ≤ 27`). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.UclkMom
open WaveTurbulence WaveTurbulence.Represents WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS Finset TTree Reg Reg.Skeleton
open scoped ENNReal

/-- Per-slot bound (copy-generalization of `prod_one_add_abs_le_maxBracketPow`): two clock losses of exponent `c`
and one extra factor of exponent `e` at clock `j` are paid by `27 ⟨m/2⟩^θ`. -/
theorem prod_one_add_abs_mul_le_maxBracketPow (m : Fin 2 → ℤ) (j : Fin 2) {c e θ : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hθ : 2 * c + e ≤ θ) :
    ENNReal.ofReal ((∏ i, (1 + |(m i : ℝ)|) ^ c) * (1 + |(m j : ℝ)|) ^ e) ≤ 27 * maxBracketPow θ (half m) := by
  unfold maxBracketPow half
  set X : ℝ := (⨆ i, Real.sqrt (1 + ((m i : ℝ) / 2) ^ 2)) ⊔ 1 with hX
  have hX1 : 1 ≤ X := le_sup_right
  have hbdd : BddAbove (Set.range fun i : Fin 2 => Real.sqrt (1 + ((m i : ℝ) / 2) ^ 2)) :=
    (Set.finite_range _).bddAbove
  have hi : ∀ i, 1 + |(m i : ℝ)| ≤ 3 * X := fun i =>
    (one_add_abs_int_le (m i)).trans (mul_le_mul_of_nonneg_left
      ((le_ciSup hbdd i).trans le_sup_left) (by norm_num))
  have hX0 : 0 < 3 * X := by linarith
  have h1 : ∏ i, (1 + |(m i : ℝ)|) ^ c ≤ (3 * X) ^ c * (3 * X) ^ c := by
    rw [Fin.prod_univ_two]
    exact mul_le_mul (Real.rpow_le_rpow (by positivity) (hi 0) hc) (Real.rpow_le_rpow (by positivity) (hi 1) hc)
      (by positivity) (by positivity)
  have h2 : (1 + |(m j : ℝ)|) ^ e ≤ (3 * X) ^ e := Real.rpow_le_rpow (by positivity) (hi j) he
  have h3 : (∏ i, (1 + |(m i : ℝ)|) ^ c) * (1 + |(m j : ℝ)|) ^ e ≤ (3 : ℝ) ^ (2 * c + e) * X ^ (2 * c + e) := by
    calc _ ≤ ((3 * X) ^ c * (3 * X) ^ c) * (3 * X) ^ e :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (3 * X) ^ (2 * c + e) := by
          rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]; ring_nf
      _ = _ := Real.mul_rpow (by norm_num) (by linarith)
  have h4 : (3 : ℝ) ^ (2 * c + e) ≤ 27 := by
    calc (3 : ℝ) ^ (2 * c + e) ≤ (3 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 27 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have h5 : X ^ (2 * c + e) ≤ X ^ θ := Real.rpow_le_rpow_of_exponent_le hX1 hθ
  have h6 : (∏ i, (1 + |(m i : ℝ)|) ^ c) * (1 + |(m j : ℝ)|) ^ e ≤ 27 * X ^ θ :=
    h3.trans (mul_le_mul h4 h5 (by positivity) (by norm_num))
  calc _ ≤ ENNReal.ofReal (27 * X ^ θ) := ENNReal.ofReal_le_ofReal h6
    _ = 27 * ENNReal.ofReal (X ^ θ) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

open WaveTurbulence.Represents WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
  Reg Reg.Skeleton in
/-- **ModesMomentSel** (U-clock (U.4), uclock §14 (iv)): main's `Represents.tsum_modes_moment` with per-slot time
weights `θ s` and the extra residual-selection moment `⟨ω^{nr}⟩^{1/18}` at the slots in `sel`. -/
def ModesMomentSel : Prop :=
  ∀ {w : ℕ} {G : Garden w} {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot G → Fin 2 → ClkSrc G ⊕ J) {Λ : ReplacementSlot G → Type}
    (W : ∀ s, Λ s → ℝ), (∀ s l, 0 ≤ W s l) → ∀ (m : ∀ s, Λ s → Fin 2 → ℤ) {c : ℝ} (θ : ReplacementSlot G → ℝ)
    (nr : ReplacementSlot G → Fin 2) (sel : Finset (ReplacementSlot G)), 0 ≤ c → c ≤ 1 →
    (∀ s, 2 * c ≤ θ s) → (∀ s ∈ sel, 2 * c + 1 / 18 ≤ θ s) → ∀ (μ : ReplacementSlot G → ℝ≥0∞),
    (∀ s, ∑' l, maxBracketPow (θ s) (half (m s l)) * ENNReal.ofReal (W s l) ≤ μ s) →
    ∑' ξ : ∀ s, Λ s, ENNReal.ofReal ((∏ s, W s (ξ s)) *
      (∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
      ∏ s ∈ sel, (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (1 / 18 : ℝ)) ≤ ∏ s, (27 * μ s)

theorem modesMomentSel : ModesMomentSel := by
  classical
  intro w G J _ _ route Λ W hW m c θ nr sel hc hc1 hcθ hcθs μ hμ
  set e : ReplacementSlot G → ℝ := fun s => if s ∈ sel then 1 / 18 else 0 with he
  have he0 : ∀ s, 0 ≤ e s := fun s => by simp only [he]; split_ifs <;> norm_num
  have he1 : ∀ s, e s ≤ 1 := fun s => by simp only [he]; split_ifs <;> norm_num
  have hθe : ∀ s, 2 * c + e s ≤ θ s := fun s => by
    simp only [he]; split_ifs with h
    · exact hcθs s h
    · linarith [hcθ s]
  have hsel : ∀ ξ : ∀ s, Λ s, ∏ s ∈ sel, (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (1 / 18 : ℝ) =
      ∏ s, (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (e s) := fun ξ => by
    rw [← Finset.prod_subset (Finset.subset_univ sel) (f := fun s => (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (e s))]
    · exact Finset.prod_congr rfl fun s hs => by simp [he, hs]
    · intro s _ hs; simp [he, hs]
  have h1 : ∀ ξ : ∀ s, Λ s, ENNReal.ofReal ((∏ s, W s (ξ s)) *
      (∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
      ∏ s ∈ sel, (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (1 / 18 : ℝ)) ≤
      ∏ s, (27 * (maxBracketPow (θ s) (half (m s (ξ s))) * ENNReal.ofReal (W s (ξ s)))) := by
    intro ξ
    have hb := prod_modLam_le (fun s => m s (ξ s)) route hc
    have hp : 0 ≤ ∏ s, W s (ξ s) := Finset.prod_nonneg fun s _ => hW s _
    have hq : 0 ≤ ∏ s ∈ sel, (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (1 / 18 : ℝ) :=
      Finset.prod_nonneg fun s _ => by positivity
    rw [hsel]
    calc ENNReal.ofReal ((∏ s, W s (ξ s)) * (∏ j, (1 + |((modLam (fun s => m s (ξ s)) route j : ℤ) : ℝ)|) ^ c) *
          ∏ s, (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (e s))
        ≤ ENNReal.ofReal ((∏ s, W s (ξ s)) * (∏ s, ∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) *
          ∏ s, (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (e s)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hq' : 0 ≤ ∏ s, (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (e s) :=
            Finset.prod_nonneg fun s _ => by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hp) hq'
      _ = ENNReal.ofReal (∏ s, (W s (ξ s) * ((∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) *
            (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (e s)))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; congr 1; ring
      _ = ∏ s, ENNReal.ofReal (W s (ξ s) * ((∏ i, (1 + |((m s (ξ s) i : ℤ) : ℝ)|) ^ c) *
            (1 + |((m s (ξ s) (nr s) : ℤ) : ℝ)|) ^ (e s))) :=
          ENNReal.ofReal_prod_of_nonneg fun s _ => mul_nonneg (hW s _)
            (mul_nonneg (Finset.prod_nonneg fun i _ => by positivity) (by positivity))
      _ ≤ _ := by
          refine Finset.prod_le_prod fun s _ => ?_
          rw [ENNReal.ofReal_mul (hW s _)]
          calc _ ≤ ENNReal.ofReal (W s (ξ s)) * (27 * maxBracketPow (θ s) (half (m s (ξ s)))) := by
                gcongr
                exact prod_one_add_abs_mul_le_maxBracketPow _ _ hc hc1 (he0 s) (he1 s) (hθe s)
            _ = _ := by ring
  calc _ ≤ ∑' ξ : ∀ s, Λ s, ∏ s, (27 * (maxBracketPow (θ s) (half (m s (ξ s))) * ENNReal.ofReal (W s (ξ s)))) :=
        ENNReal.tsum_le_tsum h1
    _ = ∏ s, ∑' l, 27 * (maxBracketPow (θ s) (half (m s l)) * ENNReal.ofReal (W s l)) :=
        ennreal_tsum_pi_prod_fintype
          (fun s l => 27 * (maxBracketPow (θ s) (half (m s l)) * ENNReal.ofReal (W s l)))
    _ ≤ _ := by
        refine Finset.prod_le_prod fun s _ => ?_
        rw [ENNReal.tsum_mul_left]
        gcongr; exact hμ s

end WaveTurbulence.Flower.UclkMom
