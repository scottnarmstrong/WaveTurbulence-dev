/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.Defs
public import WaveTurbulence.Foundations.Spine.TwistClosedNR

/-! # C5b COMP-MK: the glue — regular and non-regular classes (ruling R156)

* `markedTwistClosed_filter_nonreg`: regularity is twist-invariant (main's `twistClosed_coupleSet` argument), so the
  non-regular members of a marked-twist-closed family are marked-twist-closed.
* `marked_at`: at fixed parameters, `NonregComponentBoundAtI B₁` and `RegularComponentBoundAtI B₁` give
  `MarkedComponentBoundAtI B` for `B ≥ B₁ + 1` (the factor `2` of the split is `≤ L^{d·2R}`).
* `prefixP_and_indep`: two `WTPrefixP` statements that do not read `C₁, C₂` combine.
* **`markedComponentBoundAtI_of`**: `WTPrefixP (NonregComponentBoundAtI 17999) → WTPrefixP (RegularComponentBoundAtI
  17999) → WTPrefixP (MarkedComponentBoundAtI 18000)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs Reg Reg.Skeleton LFTwist

open WaveTurbulence.Flower.ProtWhole

namespace WaveTurbulence.Flower.CompMK

/-- **Regularity is twist-invariant**: the non-regular members of a marked-twist-closed family of canonical
gardens are marked-twist-closed. -/
theorem markedTwistClosed_filter_nonreg {w p : ℕ} (A : Finset (LayeredGarden w))
    (protSk : ∀ {ι : Type} (B : LFTwist.FamilyReconstruction w ι), GBranch B.skeleton.tree → Prop)
    (hA : ∀ LG ∈ A, IsCanonGC (p + 1) LG) (hTC : MarkedTwistClosed p A protSk)
    (q : LayeredGarden w → Prop) [DecidablePred q]
    (hq : ∀ LG, q LG ↔ ∀ h : w = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) :
    MarkedTwistClosed p (A.filter q) protSk := by
  intro kind ι B Lst hprime hcan hmem hunm LH hLH
  have hmemA : B.layered ∈ A := (Finset.mem_filter.1 hmem).1
  have hnrB := (hq _).1 (Finset.mem_filter.1 hmem).2
  refine Finset.mem_filter.2 ⟨hTC kind ι B Lst hprime hcan hmemA hunm LH hLH, (hq _).2 ?_⟩
  intro hw
  subst hw
  show ¬ IsRegularCouple LH.garden
  have hnrB' : ¬ IsRegularCouple B.layered.garden := hnrB rfl
  obtain ⟨M', B', _, hbatch, rfl⟩ := hLH
  have hcpl : IsCouple B.layered.garden :=
    ((Canon.isCanonGC_iff_isCanonC (p + 1) B.layered).mp (hA _ hmemA)).1
  have hcanB' := canonObject_two (hbatch.canonical hcan)
  have hnt : ¬ IsTrivialGarden B.skeleton := fun ht =>
    hnrB' ((couple_regular_iff_of_reconstruction B hprime hcpl).mpr ht)
  obtain ⟨hprime', hnt'⟩ := hbatch.prime_nontrivial hprime hnt
  intro hreg
  exact hnt' ((couple_regular_iff_of_reconstruction B' hprime' hcanB'.1).mp hreg)

/-- `2·L^{B₁ d·2R} ≤ L^{B d·2R}` for `B ≥ B₁ + 1`, `L ≥ 2`, `d, R ≥ 1`. -/
theorem two_rpow_le {L B₁ B : ℝ} {d R : ℕ} (hL : 2 ≤ L) (hd : 1 ≤ d) (hR : 1 ≤ R) (hB : B₁ + 1 ≤ B) :
    2 * L ^ (B₁ * d * ((2 * R : ℕ) : ℝ)) ≤ L ^ (B * d * ((2 * R : ℕ) : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hR1' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hR' : (2 : ℝ) ≤ ((2 * R : ℕ) : ℝ) := by push_cast; linarith
  have hexp : B₁ * d * ((2 * R : ℕ) : ℝ) + 1 ≤ B * d * ((2 * R : ℕ) : ℝ) := by
    have h1 : (B - B₁) * d * ((2 * R : ℕ) : ℝ) ≥ 1 * 1 * 2 := by
      apply mul_le_mul (mul_le_mul (by linarith) hd' zero_le_one (by linarith)) hR' (by norm_num)
        (by nlinarith)
    nlinarith
  calc 2 * L ^ (B₁ * d * ((2 * R : ℕ) : ℝ)) ≤ L ^ (1 : ℝ) * L ^ (B₁ * d * ((2 * R : ℕ) : ℝ)) := by
        rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL0.le _)
    _ = L ^ (B₁ * d * ((2 * R : ℕ) : ℝ) + 1) := by rw [← Real.rpow_add hL0]; ring_nf
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 hexp

/-- **The glue at fixed parameters.** -/
theorem marked_at {Pm : ℕ} {P : WTParams} (hL : 2 ≤ P.L) (hd : 1 ≤ P.d) (hδ : 0 < P.δ) {B₁ B : ℝ} (hB : B₁ + 1 ≤ B)
    (hNR : NonregComponentBoundAtI B₁ Pm P) (hReg : RegularComponentBoundAtI B₁ Pm P) :
    MarkedComponentBoundAtI B Pm P := by
  intro hγ p hp R hR1 hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel A hA hplain hTC h b hb hh Rf σ Rs dag hRf hRs
    hhigh
  have hL0 : 0 < P.L := by linarith
  set Qp : ℝ := ∏ j : Fin (2 * R), (if (kSel j).isSome then (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) else 1) with hQp
  have hRs0 : ∀ j, 0 < Rs j := fun j => lt_of_lt_of_le hL0 (hRs j)
  have hQp0 : 0 ≤ Qp := Finset.prod_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg (inv_nonneg.2 (hRs0 j).le) (Real.rpow_nonneg (hRs0 j).le _)
    · exact zero_le_one
  have hrest : 0 ≤ P.δ ^ (7 * P.ν * n) * b ^ n * Qp :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hδ.le _) (pow_nonneg (by linarith) _)) hQp0
  have h2 := two_rpow_le (B₁ := B₁) (B := B) (d := P.d) hL hd hR1 hB
  have hpos1 : 0 ≤ P.L ^ (B₁ * P.d * ((2 * R : ℕ) : ℝ)) := Real.rpow_nonneg hL0.le _
  have hone : P.L ^ (B₁ * P.d * ((2 * R : ℕ) : ℝ)) ≤ P.L ^ (B * P.d * ((2 * R : ℕ) : ℝ)) := by linarith
  by_cases hR : R = 1
  · subst hR
    set reg : LayeredGarden (2 * 1) → Prop := fun LG => ∀ hw : 2 * 1 = 2, IsRegularCouple (hw ▸ LG.garden : Garden 2)
      with hreg
    rw [← Finset.sum_filter_add_sum_filter_not A reg]
    have hreg_le := hReg hγ p hp 1 rfl hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel (A.filter reg)
      (fun LG hLG => ⟨(hA LG (Finset.mem_filter.1 hLG).1).1, (hA LG (Finset.mem_filter.1 hLG).1).2.1,
        (hA LG (Finset.mem_filter.1 hLG).1).2.2.1, (hA LG (Finset.mem_filter.1 hLG).1).2.2.2.1,
        (hA LG (Finset.mem_filter.1 hLG).1).2.2.2.2, (Finset.mem_filter.1 hLG).2⟩) hplain h b hb hh Rf σ Rs dag
      hRf hRs hhigh
    have hnr_le := hNR hγ p hp 1 hR1 hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel (A.filter fun LG => ¬ reg LG)
      (fun LG hLG => ⟨(hA LG (Finset.mem_filter.1 hLG).1).1, (hA LG (Finset.mem_filter.1 hLG).1).2.1,
        (hA LG (Finset.mem_filter.1 hLG).1).2.2.1, (hA LG (Finset.mem_filter.1 hLG).1).2.2.2.1,
        (hA LG (Finset.mem_filter.1 hLG).1).2.2.2.2, fun hw hr => (Finset.mem_filter.1 hLG).2 fun _ => hr⟩)
      hplain (markedTwistClosed_filter_nonreg A _ (fun LG hLG => (hA LG hLG).1.1) hTC (fun LG => ¬ reg LG)
        fun LG => ⟨fun h1 hw hr => h1 fun _ => hr, fun h1 h2 => h1 rfl (h2 rfl)⟩) h b hb hh Rf σ Rs dag hRf hRs hhigh
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ P.L ^ (B₁ * P.d * ((2 * 1 : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * n) * b ^ n * Qp +
          P.L ^ (B₁ * P.d * ((2 * 1 : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * n) * b ^ n * Qp := add_le_add hreg_le hnr_le
      _ = (2 * P.L ^ (B₁ * P.d * ((2 * 1 : ℕ) : ℝ))) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp) := by ring
      _ ≤ P.L ^ (B * P.d * ((2 * 1 : ℕ) : ℝ)) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp) :=
          mul_le_mul_of_nonneg_right h2 hrest
      _ = _ := by ring
  · have hnr_le := hNR hγ p hp R hR1 hR2 n hn1 hn2 t ht s hs J roots hJ pat kSel A
      (fun LG hLG => ⟨(hA LG hLG).1, (hA LG hLG).2.1, (hA LG hLG).2.2.1, (hA LG hLG).2.2.2.1,
        (hA LG hLG).2.2.2.2, fun hw => absurd (by omega : R = 1) hR⟩) hplain hTC h b hb hh Rf σ Rs dag hRf hRs hhigh
    refine hnr_le.trans ?_
    calc P.L ^ (B₁ * P.d * ((2 * R : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * n) * b ^ n * Qp
        = P.L ^ (B₁ * P.d * ((2 * R : ℕ) : ℝ)) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp) := by ring
      _ ≤ P.L ^ (B * P.d * ((2 * R : ℕ) : ℝ)) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp) :=
          mul_le_mul_of_nonneg_right hone hrest
      _ = _ := by ring

/-- **Combining two `WTPrefixP` statements that do not read the large constants `C₁, C₂`.** -/
theorem prefixP_and_indep {Q₁ Q₂ Q : ℕ → WTParams → Prop} (h₁ : WTPrefixP Q₁) (h₂ : WTPrefixP Q₂)
    (_hi₁ : ∀ Pm (P : WTParams) (c₁ c₂ : ℝ), Q₁ Pm {P with C₁ := c₁, C₂ := c₂} → Q₁ Pm P)
    (hi₂ : ∀ Pm (P : WTParams) (c₁ c₂ : ℝ), Q₂ Pm {P with C₁ := c₁, C₂ := c₂} → Q₂ Pm P)
    (step : ∀ Pm (P : WTParams), 3 ≤ P.d → 2 ≤ P.L → 0 < P.δ → Q₁ Pm P → Q₂ Pm P → Q Pm P) : WTPrefixP Q := by
  intro d hd γ hγ
  obtain ⟨η₁, hη₁, H1⟩ := h₁ d hd γ hγ
  obtain ⟨η₂, hη₂, H2⟩ := h₂ d hd γ hγ
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁a, hC₁a, ν₁, hν₁, H1⟩ := H1 η ⟨hη.1, hη.2.trans (min_le_left _ _)⟩ φin hφin τ hτ φ hsol
  obtain ⟨C₁b, hC₁b, ν₂, hν₂, H2⟩ := H2 η ⟨hη.1, hη.2.trans (min_le_right _ _)⟩ φin hφin τ hτ φ hsol
  refine ⟨C₁a, hC₁a, min ν₁ ν₂, lt_min hν₁ hν₂, fun ν hν => ?_⟩
  obtain ⟨P₁, H1⟩ := H1 ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩
  obtain ⟨P₂, H2⟩ := H2 ν ⟨hν.1, hν.2.trans (min_le_right _ _)⟩
  refine ⟨max P₁ P₂, fun Pm hPm => ?_⟩
  obtain ⟨δ₁, hδ₁, H1⟩ := H1 Pm ((le_max_left _ _).trans hPm)
  obtain ⟨δ₂, hδ₂, H2⟩ := H2 Pm ((le_max_right _ _).trans hPm)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂a, hC₂a, L₁, hL₁, H1⟩ := H1 δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD htime
  obtain ⟨C₂b, hC₂b, L₂, hL₂, H2⟩ := H2 δ ⟨hδ.1, hδ.2.trans (min_le_right _ _)⟩ D hD htime
  refine ⟨C₂a, hC₂a, max L₁ L₂, hL₁.trans (le_max_left _ _), fun L hL => ?_⟩
  have q1 := H1 L ((le_max_left _ _).trans hL)
  have q2 := H2 L ((le_max_right _ _).trans hL)
  refine step Pm _ hd (hL₁.trans ((le_max_left _ _).trans hL)) hδ.1 q1 ?_
  exact hi₂ Pm ⟨d, γ, η, φin, τ, φ, C₁a, ν, δ, D, C₂a, L⟩ C₁b C₂b q2

theorem nonregComponentBoundAtI_indep (B : ℝ) (Pm : ℕ) (P : WTParams) (c₁ c₂ : ℝ)
    (h : NonregComponentBoundAtI B Pm {P with C₁ := c₁, C₂ := c₂}) : NonregComponentBoundAtI B Pm P := by
  simpa only [NonregComponentBoundAtI, MkCarries, compValue, N_largeConstants] using h

theorem regularComponentBoundAtI_indep (B : ℝ) (Pm : ℕ) (P : WTParams) (c₁ c₂ : ℝ)
    (h : RegularComponentBoundAtI B Pm {P with C₁ := c₁, C₂ := c₂}) : RegularComponentBoundAtI B Pm P := by
  simpa only [RegularComponentBoundAtI, MkCarries, compValue, N_largeConstants] using h

/-- **The glue** (brief item 2): the non-regular part and D6b's regular part give the per-component bound at
`B = 18000` (each at `17999`). -/
theorem markedComponentBoundAtI_of (hNR : WTPrefixP (NonregComponentBoundAtI 17999))
    (hReg : WTPrefixP (RegularComponentBoundAtI 17999)) : WTPrefixP (MarkedComponentBoundAtI 18000) :=
  prefixP_and_indep hNR hReg (nonregComponentBoundAtI_indep 17999) (regularComponentBoundAtI_indep 17999)
    fun _ _ hd hL hδ h1 h2 => marked_at hL (by omega) hδ (by norm_num) h1 h2

end WaveTurbulence.Flower.CompMK
