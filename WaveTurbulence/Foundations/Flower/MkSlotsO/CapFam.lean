/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapBox

/-! # B3s-HELPER8 / CAP: one cap slot family from a superposition along the chain clock, and the mass

* `capKg`: the constant of the cap kind (centring × Fourier constants at `θ = η` and `θ = 1/4`);
* `slotFam1_of_sup`: a superposition of `G` along `(x, p)`, `x ∈ [p, p + 1]`, with the slot kernel `= G (ts j0)` on
  the general box (whose chain clock is in `[p, p + 1]`), gives `SlotFam1` at the cap momentum (B3s's `capSup_box`,
  `cap_centre`);
* `slotFam1_of_const`: a slot kernel that is constant on the box gives `SlotFam1` with one mode;
* `capMassG_le` (B3s's `capMass_le` with a general loss factor `Λ`, copied by source), `genSlotMass_cap` (the slot
  mass of a cap pair carrying a protected native node), `capMass_final`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-! ### The constant -/

/-- **The constant of the cap kind.** -/
def capKg (d : ℕ) (η : ℝ) : ℝ := capKcen d * max 1 (2 * max (capCsup d η).toReal (capCsup d (1 / 4)).toReal)

theorem one_le_capKg (d : ℕ) (η : ℝ) : 1 ≤ capKg d η :=
  one_le_mul_of_one_le_of_one_le (one_le_capKcen d) (le_max_left _ _)

theorem capKcen_le_capKg (d : ℕ) (η : ℝ) : capKcen d ≤ capKg d η :=
  le_mul_of_one_le_right (le_trans zero_le_one (one_le_capKcen d)) (le_max_left _ _)

theorem capKg_eta (d : ℕ) (η : ℝ) : capKcen d * (2 * (capCsup d η).toReal) ≤ capKg d η :=
  mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans (le_max_right _ _))
    (le_trans zero_le_one (one_le_capKcen d))

theorem capKg_quarter (d : ℕ) (η : ℝ) : capKcen d * (2 * (capCsup d (1 / 4)).toReal) ≤ capKg d η :=
  mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)).trans (le_max_right _ _))
    (le_trans zero_le_one (one_le_capKcen d))

theorem capKg_half (d : ℕ) (η : ℝ) : capKcen d * (2 * (1 / 2)) ≤ capKg d η := by
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, mul_one]
  exact capKcen_le_capKg d η

/-! ### The mass -/

/-- B3s's `capMass_le` with a general loss factor `Λ` (copied by source). -/
theorem capMassG_le (P : WTParams) (C : ℝ) (hC : P.C₁ ≤ C) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (Kcen Cs Kc : ℝ) (hKcen : 0 ≤ Kcen) (hCs : 0 ≤ Cs)
    (hKc : Kcen * (2 * Cs) ≤ Kc) (ns nr : ℕ) (hns : ns ≤ nr) (n g : ℕ) (hn : 1 ≤ n) (LSb Λ : ℝ) (hLSb : 0 ≤ LSb)
    (hΛ : 0 ≤ Λ) :
    ENNReal.ofReal Kcen * (ENNReal.ofReal Cs * (2 * (ENNReal.ofReal (frontierConst P.d ^ ns) *
        ENNReal.ofReal Λ * regBound P n g * ENNReal.ofReal LSb))) ≤
      ENNReal.ofReal (Kc * (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) *
        (frontierConst P.d ^ nr * LSb) * Λ) := by
  have hcF := one_le_frontierConst P.d
  have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one hcF
  set R := P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (g : ℝ))
  have hR : 0 ≤ R := by
    have : 0 ≤ P.C₁ := le_trans zero_le_one hC1
    positivity
  have hreg : regBound P n g = ENNReal.ofReal R := rfl
  rw [hreg, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  rw [← ENNReal.ofReal_mul (pow_nonneg hcF0 _), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul hCs, ← ENNReal.ofReal_mul hKcen]
  refine ENNReal.ofReal_le_ofReal ?_
  have hR' := capRegBound_le P C hC hC1 hδ hL hηγ n g hn
  have hpow : frontierConst P.d ^ ns ≤ frontierConst P.d ^ nr := pow_le_pow_right₀ hcF hns
  have hAB : 0 ≤ (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) := by
    have : 0 ≤ C * Real.sqrt P.δ := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    positivity
  have hK0 : 0 ≤ Kc := le_trans (by positivity) hKc
  calc Kcen * (Cs * (2 * (frontierConst P.d ^ ns * Λ * R * LSb)))
      = (Kcen * (2 * Cs)) * frontierConst P.d ^ ns * R * LSb * Λ := by ring
    _ ≤ Kc * frontierConst P.d ^ nr * ((C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ))) * LSb * Λ := by
        gcongr
    _ = Kc * (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) * (frontierConst P.d ^ nr * LSb) * Λ := by
        ring

/-- **The mass comparison with the slot mass**: a loss `Λ ≤ Lf · Π` (with the slot mass's protected loss `Lf` and
selection gain `Π`) is absorbed. -/
theorem capMass_final (P : WTParams) (C : ℝ) (hC : P.C₁ ≤ C) (hC1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 1 ≤ P.L)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (Cs Kg : ℝ) (hCs : 0 ≤ Cs) (hKg : capKcen P.d * (2 * Cs) ≤ Kg)
    (ns nr : ℕ) (hns : ns ≤ nr) (n g : ℕ) (hn : 1 ≤ n) (LSb Λ Lf Pi : ℝ) (hLSb : 0 ≤ LSb) (hΛ : 0 ≤ Λ)
    (hΛf : Λ ≤ Lf * Pi) :
    ENNReal.ofReal (capKcen P.d) * (ENNReal.ofReal Cs * (2 * (ENNReal.ofReal (frontierConst P.d ^ ns) *
        ENNReal.ofReal Λ * regBound P n g * ENNReal.ofReal LSb))) ≤
      ENNReal.ofReal (Kg * ((C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) *
        (frontierConst P.d ^ nr * LSb) * Lf * Pi)) := by
  have hK0 : 0 ≤ capKcen P.d := le_trans zero_le_one (one_le_capKcen P.d)
  refine (capMassG_le P C hC hC1 hδ hL hηγ (capKcen P.d) Cs Kg hK0 hCs hKg ns nr hns n g hn LSb Λ hLSb hΛ).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hKg0 : 0 ≤ Kg := le_trans (by positivity) hKg
  have hcF0 : 0 ≤ frontierConst P.d := le_trans zero_le_one (one_le_frontierConst P.d)
  have hA : 0 ≤ Kg * (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) * (frontierConst P.d ^ nr * LSb) := by
    have : 0 ≤ C * Real.sqrt P.δ := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have : 0 ≤ P.L ^ (-(P.η ^ 8) * (g : ℝ)) := Real.rpow_nonneg (by linarith) _
    positivity
  calc Kg * (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) * (frontierConst P.d ^ nr * LSb) * Λ
      ≤ Kg * (C * Real.sqrt P.δ) ^ (2 * n) * P.L ^ (-(P.η ^ 8) * (g : ℝ)) * (frontierConst P.d ^ nr * LSb) *
          (Lf * Pi) := mul_le_mul_of_nonneg_left hΛf hA
    _ = _ := by ring

/-- The slot mass of a cap pair carrying a protected native node. -/
theorem genSlotMass_cap (P : WTParams) (C b : ℝ) {R : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (q : SourcePair a.prime.skeleton) (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q)
    (hprot : HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (protI (recLG a) J pat t s kSel) (.inl q)) :
    genSlotMass P C b a J pat t s kSel Rs (.inl q) =
      (C * Real.sqrt P.δ) ^ slotSize a.prime.data (.inl q) *
        P.L ^ (-(P.η ^ 8) * (slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
          (.inl q) : ℝ)) *
        (frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q) *
          (b⁻¹ * slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            (fun _ => b.toNNReal) (.inl q))) *
        P.L ^ genLossExp P.d *
        ∏ v ∈ MkSlotsS.selNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel
          (.inl q), Rs v.1.1 ^ (-(1 / 18 : ℝ)) := by
  unfold genSlotMass genLeaf
  simp only [hq, hprot, ↓reduceIte]

/-! ### Families -/

section Fam

variable (P : WTParams) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R))
    (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ)
    (Rs : Fin (2 * R) → ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (q : SourcePair a.prime.skeleton) (x : Fin P.d → ℤ)

/-- **One cap slot family from a superposition along the chain clock.** -/
theorem slotFam1_of_sup (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q) (θ : ℝ) (hθ : 0 ≤ θ) (j0 : Fin 2)
    (G : ℝ → ℂ) (wt : (Fin 2 → ℤ) → ℝ) (u : (Fin 2 → ℤ) → ℂ) (hw0 : ∀ m, 0 ≤ wt m) (hws : Summable wt)
    (hu : ∀ m, ‖u m‖ ≤ 1)
    (hsum : ∀ y ∈ Icc (p : ℝ) (p + 1), HasSum (fun m => (wt m : ℂ) * u m * fsPhase m ![y, p]) (G y))
    (hB : ∀ ts ∈ genBoxAt p a J pat t s (.inl q), ts j0 ∈ Icc (p : ℝ) (p + 1))
    (hker : ∀ ts ∈ genBoxAt p a J pat t s (.inl q),
      genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts
        (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) = G (ts j0))
    (μ : ℝ≥0∞) (hμ : ENNReal.ofReal (capKcen P.d) * ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (wt m) ≤ μ) :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inl q) x θ μ := by
  set k₀ := latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) with hk₀
  obtain ⟨hu', hbox⟩ := capSup_box j0 (p : ℝ) G wt u id hu hsum (genBoxAt p a J pat t s (.inl q)) hB
  obtain ⟨c, amp, hw0', hws', hamp1, hampS, hampc, hsum', hmass'⟩ :=
    (Classical.choose_spec (cap_centre P.d)).2 θ (genBoxAt p a J pat t s (.inl q))
      (fun ts => genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts k₀) k₀ wt
      (fun m => capMode j0 (id m)) (fun m => u m * fsPhase (id m) ![0, p]) hw0 hws hu'
      (fun ts hts => by rw [hker ts hts]; exact hbox ts hts)
  refine ⟨Fin 2 → ℤ, inferInstance, fun l => capKcen P.d * wt l, fun l => capMode j0 l, c, amp, hw0', hws', hamp1,
    hampS, fun _ _ => hampc, fun ts hts n hn _ _ => ?_, ?_⟩
  · rw [hn q rfl hq]
    exact hsum' ts hts
  · refine (le_of_eq hmass').trans (le_trans ?_ hμ)
    exact mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun m => mul_le_mul' (maxBracketPow_capMode_le hθ j0 m) le_rfl)

/-- **One cap slot family from a constant kernel** (one mode `m = 0`). -/
theorem slotFam1_of_const (hq : IsCapPair a.prime.skeleton a.prime.prime.1 J q) (θ : ℝ) (V : ℂ)
    (hker : ∀ ts ∈ genBoxAt p a J pat t s (.inl q),
      genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts
        (latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q))) = V)
    (μ : ℝ≥0∞) (hμ : ENNReal.ofReal (capKcen P.d) * ‖V‖ₑ ≤ μ) :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inl q) x θ μ := by
  set k₀ := latticePoint P.L (roots (capTreeOf a.prime.skeleton a.prime.prime.1 J q)) with hk₀
  set u : ℂ := if V = 0 then 0 else V / (‖V‖ : ℂ) with hu
  have hu1 : ‖u‖ ≤ 1 := by
    rw [hu]
    split_ifs with hV0
    · simp
    · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hV0)]
  have hwu : (‖V‖ : ℂ) * u = V := by
    rw [hu]
    split_ifs with hV0
    · rw [hV0]; simp
    · have : (‖V‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hV0)
      field_simp
  obtain ⟨c, amp, hw0', hws', hamp1, hampS, hampc, hsum', hmass'⟩ :=
    (Classical.choose_spec (cap_centre P.d)).2 θ (genBoxAt p a J pat t s (.inl q))
      (fun ts => genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts k₀) k₀
      (fun _ : Unit => ‖V‖) (fun _ => 0) (fun _ => u) (fun _ => norm_nonneg _) Summable.of_finite
      (fun _ => hu1) (fun ts hts => by
        have hs := hasSum_single (f := fun l : Unit => ((‖V‖ : ℝ) : ℂ) * u * fsPhase 0 ts) ()
          (fun b' hb' => absurd (Subsingleton.elim b' ()) hb')
        have hv : ((‖V‖ : ℝ) : ℂ) * u * fsPhase 0 ts =
            genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts k₀ := by
          rw [fsPhase_zero', mul_one, hwu, hker ts hts]
        rw [← hv]
        exact hs)
  refine ⟨Unit, inferInstance, fun _ => capKcen P.d * ‖V‖, fun _ => 0, c, amp, hw0', hws', hamp1, hampS,
    fun _ _ => hampc, fun ts hts n hn _ _ => ?_, ?_⟩
  · rw [hn q rfl hq]
    exact hsum' ts hts
  · refine (le_of_eq hmass').trans (le_trans ?_ hμ)
    rw [tsum_eq_single () (fun b' hb' => absurd (Subsingleton.elim b' ()) hb'), maxBracketPow_zero, one_mul,
      ofReal_norm]
    exact le_rfl

end Fam

end WaveTurbulence.Flower.MkSlotsO
