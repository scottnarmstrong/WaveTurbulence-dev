/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Top.Fam
public import WaveTurbulence.Foundations.Flower.MkAsm.Top

/-! # FLOWER-LOW (packet L8), item B (4/6): the cores from the marked component bound, `0 < γ ≤ 1/2`

Main's `Flower.MkAsm.*` γ-carrying declarations copied by source, `1 / 2 < P.γ` ↦ `P.γ ≤ 1 / 2`, names suffixed
`Low` (`MkAsm.flower_v3_of_marked` ↦ `flower_low_of_marked`); the conditional helpers `CapsDecompFAtLow`,
`CapsDecompGAtLow` are discharged in `Top/Caps.lean` as on main. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- **Conditional helper F** at fixed `(Pm, P)` (CAPS-ID + CAPS-COMP, filtered case). -/
def CapsDecompFAtLow (Pm : ℕ) (P : WTParams) : Prop :=
  0 < P.L → P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
      (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d))
      (h : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
      (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    ∀ (Rf : Fin (2 * Pm) → Option ℝ) (σ : Fin (2 * Pm) → Option ℕ),
      (∀ j r, Rf j = some r → P.L / 2 ≤ r) →
      ((∃ i, σ i ≠ none) → ∀ j, ∃ r, Rf j = some r ∧
        (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L n‖) →
    ∃ (Str : Type) (_ : Fintype Str) (m : Str → ℕ) (D : ∀ x : Str, Fin (m x) → CompData P p t s b),
      (Fintype.card Str : ℝ) ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (2 * Pm) ∧
      (∀ x, ∑ c, 2 * (D x c).R = 4 * Pm) ∧
      (∀ x, ∑ c, (D x c).n = N) ∧
      (∀ x c j, (D x c).kSel j = none) ∧
      FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
        (fun LG k => Typed.frontierW LG p Rf k * Cases.stemFilter LG P.L σ k * Typed.leafProd LG h k)
        ζ t s n n' = ∑ x, ∏ c, (D x c).val

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- **Conditional helper F** (all parameters). -/
def CapsDecompFLow : Prop :=
  ∀ (Pm : ℕ) (P : WTParams), CapsDecompFAtLow Pm P

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- **Conditional helper G** at fixed `(Pm, P)` (CAPS-ID + CAPS-COMP + `R`-exchange, selected-face case). -/
def CapsDecompGAtLow (Pm : ℕ) (P : WTParams) : Prop :=
  0 < P.L → P.γ ≤ 1 / 2 → ∀ p : ℕ, p < P.D →
    ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d))
      (h : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ) (b : ℝ), 1 ≤ b →
      (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    ∀ (Rf : Fin (2 * Pm) → ℝ) (j₂ : ℕ), 0 < j₂ → (∀ j, P.L / 2 ≤ Rf j) →
      (∀ j, (∀ j' x, ‖x‖ ≥ Rf j → h p j j' x = 0 ∧ h p j' j x = 0) ∧
        Rf j ^ 10 ≤ ‖latticePoint P.L n‖) →
    ∃ (Str : Type) (_ : Fintype Str) (m : Str → ℕ)
      (D : (Fin (2 * Pm) → ℝ) → ∀ x : Str, Fin (m x) → CompData P p t s b),
      (Fintype.card Str : ℝ) ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) ∧
      (∀ Rs ∈ shellBox (2 * Pm) P.L j₂, ∀ x,
        (∑ c, 2 * (D Rs x c).R = 4 * Pm) ∧ (∑ c, (D Rs x c).n = N) ∧
        ((∀ c, (D Rs x c).A.Nonempty) →
          ∏ c, (D Rs x c).gain = ∏ j : Fin (2 * Pm), ((Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))))) ∧
      FC23.flowerWeighted P (fun _ _ => 1) p N kind (fun _ => .plain) dagger
        (fun LG k => Typed.frontierW LG p (fun j => some (Rf j)) k * LG.cutWeight2P P.L j₂ k *
          Typed.leafProd LG h k) ζ t s n n' =
        ∫ Rs in shellBox (2 * Pm) P.L j₂, ∑ x, ∏ c, (D Rs x c).val

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- **Conditional helper G** (all parameters). -/
def CapsDecompGLow : Prop :=
  ∀ (Pm : ℕ) (P : WTParams), CapsDecompGAtLow Pm P

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open WaveTurbulence.Flower.MkAsm.CompData
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs
variable {P : WTParams} {p : ℕ} {t s b : ℝ}

/-- The per-component bound, from `MarkedComponentBoundAtILow`. -/
theorem norm_val_leLow {B : ℝ} {Pm : ℕ} (hM : MarkedComponentBoundAtILow B Pm P)
    (hγ : P.γ ≤ 1 / 2) {p : ℕ} (hp : p < P.D) {t s b : ℝ} (ht : t ∈ Ioo (p : ℝ) (p + 1))
    (hs : s ∈ Ioo (p : ℝ) t) (hb : 1 ≤ b) (D : CompData P p t s b)
    (hR2 : D.R ≤ 2 * Pm) (hn : D.n ≤ P.N (p + 1) ^ 4) :
    ‖D.val‖ ≤ P.L ^ (B * P.d * (2 * D.R : ℕ)) * P.δ ^ (7 * P.ν * D.n) * b ^ D.n * D.gain :=
  hM hγ p hp D.R D.hR hR2 D.n D.hn hn t ht s hs D.J D.roots D.hJ D.pat D.kSel D.A D.hA D.hplain D.hclosed
    D.h b hb D.hh D.Rf D.σ D.Rs D.dag D.hRf D.hRs D.hdecay

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs
variable {P : WTParams} {p : ℕ} {t s b : ℝ}

/-- The product of the component bounds over the components of one structure: the `L`-exponent adds to
`B d (4Pm)`, the orders to `N`, and the gains multiply. -/
theorem norm_prod_val_leLow {B : ℝ} {Pm : ℕ} (hM : MarkedComponentBoundAtILow B Pm P)
    (hγ : P.γ ≤ 1 / 2) (hp : p < P.D) (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t)
    (hb : 1 ≤ b) (hL : 0 < P.L) (hδ : 0 < P.δ) {m N : ℕ} (D : Fin m → CompData P p t s b)
    (hR : ∑ c, 2 * (D c).R = 4 * Pm) (hn : ∑ c, (D c).n = N) (hN : N ≤ P.N (p + 1) ^ 4) :
    ‖∏ c, (D c).val‖ ≤
      P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N * ∏ c, (D c).gain := by
  rw [norm_prod]
  have hc : ∀ c, ‖(D c).val‖ ≤ P.L ^ (B * P.d * (2 * (D c).R : ℕ)) * P.δ ^ (7 * P.ν * (D c).n) *
      b ^ (D c).n * (D c).gain := by
    intro c
    have h2 : (D c).R ≤ 2 * Pm := by
      have := Finset.single_le_sum (f := fun c => 2 * (D c).R) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    have h3 : (D c).n ≤ P.N (p + 1) ^ 4 := by
      have := Finset.single_le_sum (f := fun c => (D c).n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
    exact norm_val_leLow hM hγ hp ht hs hb (D c) h2 h3
  have hprod : ∏ c, ‖(D c).val‖ ≤ ∏ c, (P.L ^ (B * P.d * (2 * (D c).R : ℕ)) * P.δ ^ (7 * P.ν * (D c).n) *
      b ^ (D c).n * (D c).gain) :=
    Finset.prod_le_prod₀ (fun c _ => norm_nonneg _) (fun c _ => hc c)
  refine hprod.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← Real.rpow_sum_of_pos hL, ← Real.rpow_sum_of_pos hδ, Finset.prod_pow_eq_pow_sum, hn]
  congr 3
  · rw [← Finset.mul_sum]
    congr 1
    have : ((∑ c, 2 * (D c).R : ℕ) : ℝ) = ((4 * Pm : ℕ) : ℝ) := by rw [hR]
    rw [← this]
    push_cast
    rfl
  · rw [← Finset.mul_sum]
    congr 1
    have : ((∑ c, (D c).n : ℕ) : ℝ) = (N : ℝ) := by rw [hn]
    rw [← this]
    push_cast
    rfl

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- Core-F at fixed parameters. -/
theorem coreF_atLow {B : ℝ} (hB : B ≤ 24000) {Pm : ℕ} {P : WTParams}
    (hM : MarkedComponentBoundAtILow B Pm P) (hcaps : CapsDecompFAtLow Pm P)
    (hν : 0 < P.ν) (hδ : 0 < P.δ) (hδ1 : P.δ ≤ 1) (hL : 1 ≤ P.L)
    (hthr : ∀ N p : ℕ, N ≤ P.N (p + 1) ^ 4 →
      ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) * 2 ^ Pm ≤ (P.L ^ (4000 * P.d)) ^ Pm) :
    FlowerCoreFiltAtLow BcMK Pm P := by
  intro hγ p hp t ht s hs n n' ζ N hN kind pat dagger h b hb hh Rf σ hRf hdecay
  obtain ⟨Str, _, m, D, hcard, hR, hn, hv, heq⟩ :=
    hcaps (by linarith) hγ p hp t ht s hs n n' ζ N hN kind pat dagger h b hb hh Rf σ hRf hdecay
  rw [heq]
  have hL0 : 0 < P.L := by linarith
  have hgain : ∀ x c, (D x c).gain = 1 := by
    intro x c
    simp [CompData.gain, hv]
  have hb0 : 0 ≤ b := by linarith
  have hstruct : ∀ x, ‖∏ c, (D x c).val‖ ≤
      P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N := by
    intro x
    have := norm_prod_val_leLow hM hγ hp ht hs hb hL0 hδ (D x) (hR x) (hn x) hN
    simpa [hgain] using this
  have hsum : ‖∑ x, ∏ c, (D x c).val‖ ≤
      (Fintype.card Str : ℝ) * (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x, ‖∏ c, (D x c).val‖ ≤ ∑ _x : Str, (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) *
          P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N) := Finset.sum_le_sum fun x _ => hstruct x
      _ = _ := by simp
  refine hsum.trans ?_
  have hcnt : (Fintype.card Str : ℝ) ≤ (P.L ^ (4000 * P.d)) ^ Pm := by
    refine hcard.trans ?_
    refine le_trans ?_ (hthr N p hN)
    have : (1 : ℝ) ≤ 2 ^ Pm := one_le_pow₀ (by norm_num)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
    have hpow : ((N : ℝ) + 1) ^ (2 * Pm) ≤ ((N : ℝ) + 1) ^ (4 * Pm) := pow_le_pow_right₀ hN1 (by omega)
    have h4 : (0 : ℝ) ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) := by positivity
    have hnn : 0 ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) := by positivity
    calc ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (2 * Pm)
        ≤ ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) := mul_le_mul_of_nonneg_left hpow h4
      _ ≤ _ := by nlinarith
  have habs := absorb_L (d := P.d) (Pm := Pm) hL hB hcnt
  have hdel := delta_mono (N := N) hδ hδ1 hν
  have hbN : 0 ≤ b ^ N := by positivity
  have hLB : 0 ≤ P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) := by positivity
  have hδN : 0 ≤ P.δ ^ (7 * P.ν * (N : ℝ)) := by positivity
  calc (Fintype.card Str : ℝ) * (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N)
      = ((Fintype.card Str : ℝ) * P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ))) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N := by ring
    _ ≤ P.L ^ (BcMK P.d * (Pm : ℝ)) * P.δ ^ (6 * P.ν * (N : ℝ)) * b ^ N := by
        have h1 : (Fintype.card Str : ℝ) * P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) ≤ P.L ^ (BcMK P.d * (Pm : ℝ)) :=
          habs
        gcongr

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- Core-G at fixed parameters. -/
theorem coreG_atLow {B : ℝ} (hB : B ≤ 24000) {Pm : ℕ} {P : WTParams}
    (hM : MarkedComponentBoundAtILow B Pm P) (hcaps : CapsDecompGAtLow Pm P)
    (hν : 0 < P.ν) (hδ : 0 < P.δ) (hδ1 : P.δ ≤ 1) (hL : 1 ≤ P.L)
    (hthr : ∀ N p : ℕ, N ≤ P.N (p + 1) ^ 4 →
      ((4 * Pm : ℕ) : ℝ) ^ (4 * Pm) * ((N : ℝ) + 1) ^ (4 * Pm) * 2 ^ Pm ≤ (P.L ^ (4000 * P.d)) ^ Pm) :
    FlowerCoreGainAtLow BcMK Pm P := by
  intro hγ p hp t ht s hs n n' ζ N hN kind dagger h b hb hh Rf j₂ hj₂ hRf hdecay
  obtain ⟨Str, _, m, D, hcard, hsum, heq⟩ :=
    hcaps (by linarith) hγ p hp t ht s hs n n' ζ N hN kind dagger h b hb hh Rf j₂ hj₂ hRf hdecay
  rw [heq]
  have hL0 : 0 < P.L := by linarith
  set a : ℝ := 2 ^ (j₂ - 1) * P.L with ha
  have ha0 : 0 < a := by positivity
  set X : ℝ := (2 : ℝ) ^ j₂ * P.L with hXdef
  have hX0 : 0 < X := by positivity
  have haX : a = X / 2 := by
    rw [ha, hXdef]
    obtain ⟨k, rfl⟩ : ∃ k, j₂ = k + 1 := ⟨j₂ - 1, by omega⟩
    simp [pow_succ]
    ring
  set K0 : ℝ := P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N with hK0
  have hb0 : 0 ≤ b := by linarith
  have hK0nn : 0 ≤ K0 := by positivity
  -- pointwise bound on the box
  have hpt : ∀ Rs ∈ shellBox (2 * Pm) P.L j₂,
      ‖∑ x, ∏ c, (D Rs x c).val‖ ≤
        (Fintype.card Str : ℝ) * K0 * (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) := by
    intro Rs hRs
    have hRj : ∀ j, a ≤ Rs j ∧ Rs j ≤ X := fun j => by
      have := hRs j (Set.mem_univ j)
      exact this
    have hstruct : ∀ x, ‖∏ c, (D Rs x c).val‖ ≤ K0 * ∏ j : Fin (2 * Pm), ((Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))) := by
      intro x
      obtain ⟨h1, h2, h3⟩ := hsum Rs hRs x
      by_cases hne : ∀ c, (D Rs x c).A.Nonempty
      · have := norm_prod_val_leLow hM hγ hp ht hs hb hL0 hδ (D Rs x) h1 h2 hN
        rw [h3 hne] at this
        exact this
      · -- an empty class has value `0`
        obtain ⟨c₀, hc₀⟩ := not_forall.1 hne
        have hA0 : (D Rs x c₀).A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hc₀
        have hv0 : (D Rs x c₀).val = 0 := by
          unfold CompData.val; rw [hA0, Finset.sum_empty]
        rw [Finset.prod_eq_zero (Finset.mem_univ c₀) hv0, norm_zero]
        have hpos : 0 ≤ ∏ j : Fin (2 * Pm), ((Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))) := by
          refine Finset.prod_nonneg fun j _ => ?_
          have hr : 0 < Rs j := lt_of_lt_of_le ha0 (hRj j).1
          positivity
        exact mul_nonneg hK0nn hpos
    have hg : ∀ j, (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) ≤ a⁻¹ * a ^ (-(1 / 18 : ℝ)) := by
      intro j
      have hr : 0 < Rs j := lt_of_lt_of_le ha0 (hRj j).1
      have h1 : (Rs j)⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 (hRj j).1
      have h2 : (Rs j) ^ (-(1 / 18 : ℝ)) ≤ a ^ (-(1 / 18 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ha0 (hRj j).1 (by norm_num)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hprod : ∏ j : Fin (2 * Pm), ((Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))) ≤
        (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) := by
      have := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin (2 * Pm))))
        (f := fun j => (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ))) (g := fun _ => a⁻¹ * a ^ (-(1 / 18 : ℝ)))
        (fun j _ => by
          have hr : 0 < Rs j := lt_of_lt_of_le ha0 (hRj j).1
          positivity) (fun j _ => hg j)
      simpa using this
    refine (norm_sum_le _ _).trans ?_
    calc ∑ x, ‖∏ c, (D Rs x c).val‖
        ≤ ∑ _x : Str, K0 * (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) :=
          Finset.sum_le_sum fun x _ => (hstruct x).trans (mul_le_mul_of_nonneg_left hprod hK0nn)
      _ = _ := by simp; ring
  -- the integral over the box
  have hvol : (volume (shellBox (2 * Pm) P.L j₂)).toReal = a ^ (2 * Pm) := by
    have : shellBox (2 * Pm) P.L j₂ = Set.Icc (fun _ : Fin (2 * Pm) => a) (fun _ => X) := by
      unfold shellBox
      exact Set.pi_univ_Icc _ _
    rw [this, Real.volume_Icc_pi_toReal (fun j => by
      show a ≤ X
      rw [haX]; linarith)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have : X - a = a := by rw [haX]; ring
    rw [this]
  have hfin : volume (shellBox (2 * Pm) P.L j₂) < ⊤ := by
    have : shellBox (2 * Pm) P.L j₂ = Set.Icc (fun _ : Fin (2 * Pm) => a) (fun _ => X) := by
      unfold shellBox
      exact Set.pi_univ_Icc _ _
    rw [this]
    exact measure_Icc_lt_top
  have hint := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun Rs : Fin (2 * Pm) → ℝ =>
    ∑ x, ∏ c, (D Rs x c).val) hfin hpt
  refine hint.trans ?_
  have hreal : volume.real (shellBox (2 * Pm) P.L j₂) = a ^ (2 * Pm) := hvol
  rw [hreal]
  -- (a⁻¹ a^{-1/18})^{2Pm} a^{2Pm} = (a^{-1/18})^{2Pm}
  have hcalc : (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) * a ^ (2 * Pm) =
      (a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hcnt : (Fintype.card Str : ℝ) * 2 ^ Pm ≤ (P.L ^ (4000 * P.d)) ^ Pm := by
    refine le_trans ?_ (hthr N p hN)
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  have habs := absorb_L (d := P.d) (Pm := Pm) hL hB hcnt
  have hdel := delta_mono (N := N) hδ hδ1 hν
  have h2le : (2 : ℝ) ^ ((Pm : ℝ) / 9) ≤ 2 ^ Pm := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (0 : ℝ) ≤ Pm := Nat.cast_nonneg _
    linarith
  have hLB : 0 ≤ P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) := by positivity
  have hδN : 0 ≤ P.δ ^ (7 * P.ν * (N : ℝ)) := by positivity
  have hbN : 0 ≤ b ^ N := by positivity
  have hXpow : 0 ≤ X ^ (-((Pm : ℝ) / 9)) := by positivity
  calc (Fintype.card Str : ℝ) * K0 * (a⁻¹ * a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm) * a ^ (2 * Pm)
      = (Fintype.card Str : ℝ) * K0 * ((a ^ (-(1 / 18 : ℝ))) ^ (2 * Pm)) := by rw [mul_assoc _ _ (a ^ (2 * Pm)) |>.symm.symm]; rw [mul_assoc, hcalc]; ring
    _ = (Fintype.card Str : ℝ) * K0 * ((2 : ℝ) ^ ((Pm : ℝ) / 9) * X ^ (-((Pm : ℝ) / 9))) := by
        rw [haX, shell_pow hX0]
    _ ≤ ((Fintype.card Str : ℝ) * 2 ^ Pm * P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ))) * P.δ ^ (7 * P.ν * (N : ℝ)) *
          b ^ N * X ^ (-((Pm : ℝ) / 9)) := by
        rw [hK0]
        have hc0 : (0 : ℝ) ≤ Fintype.card Str := Nat.cast_nonneg _
        have : (Fintype.card Str : ℝ) * (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N) *
            ((2 : ℝ) ^ ((Pm : ℝ) / 9) * X ^ (-((Pm : ℝ) / 9))) ≤
            (Fintype.card Str : ℝ) * (P.L ^ (B * P.d * ((4 * Pm : ℕ) : ℝ)) * P.δ ^ (7 * P.ν * (N : ℝ)) * b ^ N) *
            (2 ^ Pm * X ^ (-((Pm : ℝ) / 9))) := by gcongr
        calc _ ≤ _ := this
          _ = _ := by ring
    _ ≤ P.L ^ (BcMK P.d * (Pm : ℝ)) * P.δ ^ (6 * P.ν * (N : ℝ)) * b ^ N * X ^ (-((Pm : ℝ) / 9)) := by
        gcongr
    _ = _ := by rw [hXdef]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- **MK-ASM export F**: Core-F from the per-component marked bound (`MarkedComponentBoundAtILow`, at the concrete
marking rule `protSkOf`; B0 finding F-B0-1). -/
def CoreFOfComponentsLow : Prop :=
  ∀ B : ℝ, 0 ≤ B → B ≤ 24000 → WTPrefixP (MarkedComponentBoundAtILow B) →
    WTPrefixP (FlowerCoreFiltAtLow BcMK)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- **MK-ASM export G**: Core-G from the per-component marked bound. -/
def CoreGOfComponentsLow : Prop :=
  ∀ B : ℝ, 0 ≤ B → B ≤ 24000 → WTPrefixP (MarkedComponentBoundAtILow B) →
    WTPrefixP (FlowerCoreGainAtLow BcMK)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- The final consumer, as on main (`layergardenFlower_v3_of_cores`), at `BcMK`. -/
theorem flower_low_of_marked (hF : CoreFOfComponentsLow)
    (hG : CoreGOfComponentsLow) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : B ≤ 24000) (hM : WTPrefixP (MarkedComponentBoundAtILow B)) (hCouple : CoupleClauseLowInput) :
    LayergardenFlowerLowGate :=
  flower_low_of_cores BcMK BcMK_hBc (hF B hB0 hB hM) (hG B hB0 hB hM) hCouple

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

theorem coreFOfComponents_of_capsLow (hcaps : CapsDecompFLow) : CoreFOfComponentsLow := by
  intro B hB0 hB hM
  exact prefixP_of_at hM fun Pm P _ hν hδ hδ1 hL hthr hMP =>
    coreF_atLow hB hMP (hcaps Pm P) hν hδ hδ1 hL hthr

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

theorem coreGOfComponents_of_capsLow (hcaps : CapsDecompGLow) : CoreGOfComponentsLow := by
  intro B hB0 hB hM
  exact prefixP_of_at hM fun Pm P _ hν hδ hδ1 hL hthr hMP =>
    coreG_atLow hB hMP (hcaps Pm P) hν hδ hδ1 hL hthr

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkAsm
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

/-- The final consumer from the two conditional helpers and the marked component bound. -/
theorem flower_low_of_marked_of_caps (hF : CapsDecompFLow) (hG : CapsDecompGLow) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : B ≤ 24000) (hM : WTPrefixP (MarkedComponentBoundAtILow B)) (hCouple : CoupleClauseLowInput) :
    LayergardenFlowerLowGate :=
  flower_low_of_marked (coreFOfComponents_of_capsLow hF) (coreGOfComponents_of_capsLow hG) B hB0 hB hM hCouple

end

end WaveTurbulence.GammaLow.Flower
