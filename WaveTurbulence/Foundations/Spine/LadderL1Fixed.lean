/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderL1
public import WaveTurbulence.Foundations.Spine.LadderDecayFinal
/-! # The time-L1 fixed-parameter ladder bound (S3c COARSE-SPLICED)

Same parameters and arithmetic as `ladder_fixed` (S3b), with the conclusion at the level of the
time-L1 norm of the finite lattice sum, before the time ordering is used. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.WeylSums WaveTurbulence.Sumint MeasureTheory Set Finset

variable {w d : ℕ} {G : Garden w}

/-- **The time-L1 fixed-parameter ladder bound.** -/
theorem ladder_L1_fixed (hd3 : 3 ≤ d) {γ η δ τ x C0 L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) (hC0 : 0 ≤ C0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL1 : 1 ≤ L)
    (hRung : ∀ (a b : Fin d → ℝ) (χ : Pt d → ℝ), GoodTerm L (L ^ (1 - γ + η)) a b χ →
      RungOK γ x τ δ L C0 a b χ)
    {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (hlad : G.molecule.IsLadder u v)
    (hP : G.IsPlain) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (hlay : ∀ a, δ * ((D.layer a : ℝ) + 1) ≤ τ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (boundary : GardenDart G → (Fin d → ℤ))
    (T0 : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary))
    (hT0 : ∀ z, z ∉ T0 → ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 = 0) :
    ‖(coupling d L γ δ : ℂ)‖ ^ ((Molecule.ladderAtoms u v).card - 1) *
      ∫ t in timeBox G D.layer (Molecule.ladderAtoms u v),
        ‖∑ z ∈ T0, ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1.1 *
          ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1.1 t‖ ≤
      (1 + 9 * (7 ^ d * cellFourierFactor d) ^ 4 * C0 + 3 ^ (16 * d) * (7 ^ d * cellFourierFactor d) ^ 2) *
        ((1 + 9 * (7 ^ d * cellFourierFactor d) ^ 4 * C0 + 3 ^ (16 * d) * (7 ^ d * cellFourierFactor d) ^ 2) *
          δ) ^ (n + 1) *
        L ^ (-x * (sourceLadderIncoherency G D.layer u v : ℝ) + 20 * (d : ℝ)) := by
  classical
  set C := gardenCtx hlad with hC
  have hL0 : 0 < L := by linarith
  by_cases hne : Nonempty ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary)
  swap
  · have hz : T0 = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro z _
      exact hne ⟨z⟩
    rw [hz]
    simp only [Finset.sum_empty, norm_zero, MeasureTheory.integral_zero, mul_zero]
    positivity
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
  have kc0 := C.kernel_core_L1 hP hL0 base roots hn D hD (by omega) γ η δ x τ C0 hδ hC0 hρ hR hRung hlay
    boundary NC hNC T0 hT0
  have kc := mul_le_mul_of_nonneg_left kc0
    (pow_nonneg (norm_nonneg (coupling d L γ δ : ℂ)) ((Molecule.ladderAtoms u v).card - 1))
  have hcs : (Molecule.ladderAtoms u v).card - 1 = 2 * n + 3 := by
    rw [C.card_ladderAtoms]; omega
  have hcJ : Fintype.card ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) = 36 := by simp
  have hcoup : ‖(coupling d L γ δ : ℂ)‖ = δ / (2 * L ^ ((d : ℝ) - γ)) := by
    unfold coupling
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hdiff : ∀ a b : ℕ, (((a : ℝ) + 1 ≤ b ∨ (b : ℝ) + 1 ≤ a)) ↔ a ≠ b := by
    intro a b
    constructor
    · rintro (h | h) hab <;> subst hab <;> linarith
    · intro hab
      rcases lt_or_gt_of_ne hab with h | h
      · left; exact_mod_cast Nat.succ_le_of_lt h
      · right; exact_mod_cast Nat.succ_le_of_lt h
  rw [hcs, hcJ, card_code, hcoup] at kc
  have hprod := prod_rungBudget (n := n)
    (fun k => ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
      (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k)))) d γ x δ L C0
  rw [hprod] at kc
  have hfilt : (Finset.univ.filter (fun k : Fin n =>
        ((D.layer (u (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (v (LadderDarts.ir k)) ∨
          (D.layer (v (LadderDarts.ir k)) : ℝ) + 1 ≤ D.layer (u (LadderDarts.ir k))))) =
      Finset.univ.filter (fun k : Fin n => D.layer (u (LadderDarts.ir k)) ≠ D.layer (v (LadderDarts.ir k))) :=
    Finset.filter_congr (fun k _ => hdiff _ _)
  rw [hfilt] at kc
  have hinc := C.incoh_le D.layer
  have hNCle : (NC : ℝ) ≤ 2 * (3 * L) ^ (16 * d) := by
    have h1 : ((2 * L + 1) ^ d) ^ 16 ≤ (3 * L) ^ (16 * d) := by
      rw [← pow_mul, mul_comm d 16]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2 : (1 : ℝ) ≤ ((2 * L + 1) ^ d) ^ 16 := one_le_pow₀ (one_le_pow₀ (by linarith))
    have h3 := Nat.ceil_lt_add_one (a := ((2 * L + 1) ^ d) ^ 16) (by positivity)
    linarith
  rw [hcs, hcoup]
  exact final_bound hd3 hγ0 hγ1 hL1 hδ hδ1 hx0 hx1 hC0
    (by have := cellFourierFactor_nonneg d; positivity) hinc (Nat.cast_nonneg _) hNCle kc

end WaveTurbulence.LadderDecay
