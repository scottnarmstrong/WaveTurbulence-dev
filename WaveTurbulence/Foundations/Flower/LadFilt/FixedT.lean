/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.LadFilt.CoreT

/-! # C3 LAD-FILT: the fixed-parameter ladder bound on translated boxes

Copy-thread of main's `ladder_L1_fixed` (Spine/LadderL1Fixed): the time-L¹ ladder bound over the unit time box
translated by `τ`, with the constant built from `2 C₀ + 16·81^d` and the translation weight `ladderWt κ τ`
as an extra factor. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.LadFilt
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay WaveTurbulence.WeylSums
  WaveTurbulence.Sumint MeasureTheory Set Finset

variable {w d : ℕ} {G : Garden w}

/-- The ladder constant of the translated bound (main's `C₁` formula at `2 C₀ + 16·81^d`). -/
noncomputable def ladConst (d : ℕ) (C0 : ℝ) : ℝ :=
  1 + 9 * (7 ^ d * cellFourierFactor d) ^ 4 * (2 * C0 + 16 * 81 ^ d) +
    3 ^ (16 * d) * (7 ^ d * cellFourierFactor d) ^ 2

lemma one_le_ladConst (d : ℕ) {C0 : ℝ} (hC0 : 0 ≤ C0) : 1 ≤ ladConst d C0 := by
  unfold ladConst
  have hM : 0 ≤ 7 ^ d * cellFourierFactor d := by have := cellFourierFactor_nonneg d; positivity
  have : 0 ≤ 9 * (7 ^ d * cellFourierFactor d) ^ 4 * (2 * C0 + 16 * 81 ^ d) := by positivity
  have : 0 ≤ 3 ^ (16 * d) * (7 ^ d * cellFourierFactor d) ^ 2 := by positivity
  linarith

/-- **The time-L¹ fixed-parameter ladder bound on a translated box.** -/
theorem ladder_L1_fixed_T (hd3 : 3 ≤ d) {γ η δ τ1 x C0 L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (hC0 : 0 ≤ C0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL1 : 1 ≤ L)
    (hRung : ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), GoodTerm L (L ^ (1 - γ + η)) a b χ →
      RungOK γ x τ1 δ L C0 a b χ)
    (hB : δ⁻¹ * (L ^ (2 * γ))⁻¹ ≤ L ^ (-x))
    {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (hlad : G.molecule.IsLadder u v)
    (hP : G.IsPlain) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (hlay : ∀ a, δ * ((D.layer a : ℝ) + 2) ≤ τ1) (τ : (Molecule.ladderAtoms u v) → ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (boundary : GardenDart G → (Fin d → ℤ))
    (T0 : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary))
    (hT0 : ∀ z, z ∉ T0 → ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 = 0) :
    ‖(coupling d L γ δ : ℂ)‖ ^ ((Molecule.ladderAtoms u v).card - 1) *
      ∫ t in timeBoxT G D.layer (Molecule.ladderAtoms u v) τ,
        ‖∑ z ∈ T0, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
          ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ ≤
      ladderWt (u := u) (v := v) (δ * L ^ (2 * γ) / 2) τ *
        (ladConst d C0 * (ladConst d C0 * δ) ^ (n + 1) *
          L ^ (-x * (sourceLadderIncoherency G D.layer u v : ℝ) + 20 * (d : ℝ))) := by
  classical
  set C := gardenCtx hlad with hC
  have hL0 : 0 < L := by linarith
  have hκ0 : 0 ≤ δ * L ^ (2 * γ) / 2 := by
    have := Real.rpow_pos_of_pos hL0 (2 * γ); positivity
  set W := ladderWt (u := u) (v := v) (δ * L ^ (2 * γ) / 2) τ with hW
  have hW1 : 1 ≤ W := one_le_ladderWt hκ0 τ
  have hW0 : 0 < W := by linarith
  have hC1 := one_le_ladConst d hC0
  have hRHS0 : 0 ≤ ladConst d C0 * (ladConst d C0 * δ) ^ (n + 1) *
      L ^ (-x * (sourceLadderIncoherency G D.layer u v : ℝ) + 20 * (d : ℝ)) := by
    have := Real.rpow_pos_of_pos hL0 (-x * (sourceLadderIncoherency G D.layer u v : ℝ) + 20 * (d : ℝ))
    have : 0 ≤ ladConst d C0 := by linarith
    positivity
  by_cases hne : Nonempty ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary)
  swap
  · have hz : T0 = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro z _
      exact hne ⟨z⟩
    rw [hz]
    simp only [Finset.sum_empty, norm_zero, MeasureTheory.integral_zero, mul_zero]
    exact mul_nonneg hW0.le hRHS0
  obtain ⟨z⟩ := hne
  have hn : Mole.RootPairCompatible G (rootVec L base roots) :=
    Mole.rootPairCompatible_of_labels G _ (fun a => base + latticePoint L (z.1.1 a))
      (fun i => by rw [z.1.2.2.1 i]; rfl) (isDecoration_coset L base z.1.2.1).2
  have hρ : 0 ≤ L ^ (-γ + η) := (Real.rpow_pos_of_pos hL0 _).le
  have hR : L * L ^ (-γ + η) ≤ L ^ (1 - γ + η) := by
    have := Real.rpow_add hL0 1 (-γ + η)
    rw [Real.rpow_one] at this
    have e : (1 : ℝ) + (-γ + η) = 1 - γ + η := by ring
    rw [e] at this
    exact le_of_eq this.symm
  set NC : ℕ := ⌈((2 * L + 1) ^ d) ^ 16⌉₊ with hNCdef
  have hNC : ∀ T : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary),
      (∀ z ∈ T, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 ≠ 0) →
        (T.image (fun z => LadderDarts.Ctx.clsOf (u := u) (v := v) z.1)).card ≤ NC := by
    intro T hT
    have h1 := C.class_count hP hL0 base D hD γ η roots boundary T hT
    have h2 : (((T.image (fun z => LadderDarts.Ctx.clsOf (u := u) (v := v) z.1)).card : ℕ) : ℝ) ≤ (NC : ℝ) :=
      h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  have kc0 := kernel_core_L1_T C hP hL1 base roots hn D hD (by omega) γ η δ x τ1 C0 hδ hx0 hC0 hρ hR hRung hB
    hlay τ boundary NC hNC T0 hT0
  have kc := mul_le_mul_of_nonneg_left kc0
    (pow_nonneg (norm_nonneg (coupling d L γ δ : ℂ)) ((Molecule.ladderAtoms u v).card - 1))
  have hcs : (Molecule.ladderAtoms u v).card - 1 = 2 * n + 3 := by
    rw [C.card_ladderAtoms]; omega
  have hcJ : Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) = 36 := by simp
  have hcoup : ‖(coupling d L γ δ : ℂ)‖ = δ / (2 * L ^ ((d : ℝ) - γ)) := by
    unfold coupling
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  rw [hcs, hcJ, card_code, hcoup, Finset.prod_mul_distrib] at kc
  have hprod := prod_rungBudget (n := n)
    (fun k => D.layer (u (LadderDarts.ir k)) ≠ D.layer (v (LadderDarts.ir k))) d γ x δ L (2 * C0 + 16 * 81 ^ d)
  rw [hprod] at kc
  have hWe : (∏ k : Fin n, rungWt (δ * L ^ (2 * γ) / 2) (τ (LadderDarts.Ctx.evIdx (u := u) (v := v) k))
      (τ (LadderDarts.Ctx.euIdx (u := u) (v := v) k))) = W := rfl
  rw [hWe] at kc
  have hinc := C.incoh_le D.layer
  have hNCle : (NC : ℝ) ≤ 2 * (3 * L) ^ (16 * d) := by
    have h1 : ((2 * L + 1) ^ d) ^ 16 ≤ (3 * L) ^ (16 * d) := by
      rw [← pow_mul, mul_comm d 16]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2 : (1 : ℝ) ≤ ((2 * L + 1) ^ d) ^ 16 := one_le_pow₀ (one_le_pow₀ (by linarith))
    have h3 := Nat.ceil_lt_add_one (a := ((2 * L + 1) ^ d) ^ 16) (by positivity)
    linarith
  rw [hcs, hcoup]
  set K := (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n + 3) *
      ∫ t in timeBoxT G D.layer (Molecule.ladderAtoms u v) τ,
        ‖∑ z ∈ T0, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
          ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ with hK
  have hK' : K / W ≤ (δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n + 3) *
      ((NC : ℝ) * (36 ^ n * ((7 ^ d * cellFourierFactor d) ^ (4 * n + 2) *
        (((2 * C0 + 16 * 81 ^ d) * (δ⁻¹ * L ^ ((2 : ℝ) * d - 2 * γ))) ^ n *
          (L ^ (-x)) ^ (Finset.univ.filter
            (fun k : Fin n => D.layer (u (LadderDarts.ir k)) ≠ D.layer (v (LadderDarts.ir k)))).card)))) := by
    rw [div_le_iff₀ hW0]
    refine kc.trans (le_of_eq ?_)
    push_cast
    ring
  have hfin := final_bound hd3 hγ0 hγ1 hL1 hδ hδ1 hx0 hx1 (by positivity : (0 : ℝ) ≤ 2 * C0 + 16 * 81 ^ d)
    (by have := cellFourierFactor_nonneg d; positivity) hinc (Nat.cast_nonneg _) hNCle hK'
  rw [div_le_iff₀ hW0] at hfin
  have e : ladConst d C0 = 1 + 9 * (7 ^ d * cellFourierFactor d) ^ 4 * (2 * C0 + 16 * 81 ^ d) +
      3 ^ (16 * d) * (7 ^ d * cellFourierFactor d) ^ 2 := rfl
  rw [e]
  linarith

end WaveTurbulence.Flower.LadFilt
