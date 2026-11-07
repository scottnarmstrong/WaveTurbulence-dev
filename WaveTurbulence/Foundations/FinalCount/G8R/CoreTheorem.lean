/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreSplit
import Mathlib.Tactic

/-! # The core theorem of Prop 10.4(2)′

`core_split`: for every core molecule and every bond, the decoration split with `ε₁ = (|𝕄| + 1) L^{−η/4}` and
`ε₂ = (|𝕄| + 1) L^{−γ₀−η/4}`, from the named inputs of `CoreInputs`, DH23 Prop 10.2 (both statements, as inputs) and
G6's Props 10.1 and 10.3. Smallness of `η`: `η ≤ γ₀/200` (G6's Prop 10.3) and `dη ≤ γ₀/4` (case III).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

/-- `c ≤ L^θ`, `m ≥ 1` and `θ + a ≤ b` give `c L^a ≤ m L^b`. -/
theorem absorb' {L θ c m a b : ℝ} (hL : 1 ≤ L) (hc : c ≤ L ^ θ) (hm : 1 ≤ m) (hab : θ + a ≤ b) :
    c * L ^ a ≤ m * L ^ b := by
  have h := absorb hL hc zero_le_one hab
  rw [one_mul, one_mul] at h
  exact h.trans (le_mul_of_one_le_left (Real.rpow_nonneg (zero_le_one.trans hL) _) hm)

/-- **The core of Prop 10.4(2)′.** -/
theorem core_split (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4) (hγ12 : 1 / 2 < γ)
    (i1 : BetaCutInput.{u, v} d γ η) (i2 : BridgeSplitInput.{u, v} d γ η) (i3 : BiBridgeInput.{u, v} d γ η)
    (i4 : BiBridgeEqualInput.{u, v} d γ η) (i5 : PairGainInput.{u, v} d γ η)
    (i6 : SmallGapPairInput.{u, v} d γ η) (i7 : MergeInput.{u, v} d γ η)
    (h102 : Prop102Input.{u, v} d γ η) (h102s : Prop102SecondInput.{u, v} d γ η) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D), IsCore M →
        (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → ∀ e : D, SplitBound M e d L γ δ η C1 ((M.atoms.card + 1) * L ^ (-(η / 4)))
          ((M.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 4))) := by
  have hg : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith [hγ.2])
  have hηmax : η ≤ min γ (1 - γ) / 2 := by linarith
  have hθ : (0 : ℝ) < η / 12 := by positivity
  have g1 := input_good (X := fun C1 δ L K B => BetaCutAt.{u, v} d L γ δ η C1 K B) hθ i1
  have g2 := input_good (X := fun C1 δ L K B => BridgeSplitAt.{u, v} d L γ δ η C1 K B) hθ i2
  have g3 := input_good (X := fun C1 δ L K B => BiBridgeAt.{u, v} d L γ δ η C1 K B) hθ i3
  have g4 := input_good (X := fun C1 δ L K B => BiBridgeEqualAt.{u, v} d L γ δ η C1 K B) hθ i4
  have g5 := input_good (X := fun C1 δ L K B => PairGainAt.{u, v} d L γ δ η C1 K B) hθ (i5 hγ12)
  have g6 := input_good_nonneg (X := fun C1 δ L K B => SmallGapPairAt.{u, v} d L γ δ η C1 K B) hθ
    (fun _ _ _ _ _ hL h => smallGapPairAt_mono hL h) (i6 hγ12)
  have g7 := input_good_nonneg (X := fun C1 δ L K B => MergeAt.{u, v} d L γ δ η C1 K B) hθ
    (fun _ _ _ _ _ hL h => mergeAt_mono hL h) (i7 hγ12 hη (by linarith))
  obtain ⟨Cs, hCs, hall⟩ := uniform_and_m (uniform_lift g1) (uniform_and_m (uniform_lift g2)
    (uniform_and_m (uniform_lift g3) (uniform_and_m (uniform_lift g4) (uniform_and_m (uniform_lift g5)
    (uniform_and_m (uniform_lift g6) (uniform_and_m (uniform_lift g7) (uniform_and_m (prop102At_of_input h102)
      (uniform_and_m (prop102SecondAt_of_input h102s)
        (uniform_and_m (uniform_lift (prop103At_of_G6.{u, v} d hd γ hγ η hη hη200))
          (uniform_lift (prop101At_of_G6.{u, v} d hd γ hγ η hη hηmax)))))))))))
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := hall m C1 hC1 δ hδ
  refine ⟨max R (Real.exp 1), fun L hL => ?_⟩
  obtain ⟨⟨K1, B1, j1, k1⟩, ⟨K2, B2, j2, k2⟩, ⟨K3, B3, j3, k3⟩, ⟨K4, B4, j4, k4⟩, ⟨K5, B5, j5, k5⟩,
    ⟨K6, B6, hK6, j6, k6⟩, ⟨K7, B7, hK7, j7, k7⟩, j8, j9, j10, j11⟩ := hR L ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  intro V D _ _ _ M hM hszM e
  suffices H : ∀ n : ℕ, ∀ {D : Type v} [Fintype D] [DecidableEq D] (M : Molecule V D), M.atoms.card = n →
      (n : ℝ) ≤ (1 + Real.log L) ^ m → IsCore M → ∀ e : D, SplitBound M e d L γ δ η C1 (((n : ℝ) + 1) * L ^ (-(η / 4)))
        (((n : ℝ) + 1) * L ^ (-(min γ (1 - γ) + η / 4))) from H _ M rfl hszM hM e
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D _ _ M hn hszn hM e
  classical
  have hsz : (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m := by rw [hn]; exact hszn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := zero_le_one.trans hn1
  -- case 0: only single bonds
  by_cases hs : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1
  · refine splitBound_mono (case_simple j10 hM e hs _) le_rfl ?_
    calc L ^ (-(min γ (1 - γ) + η / 2)) ≤ L ^ (-(min γ (1 - γ) + η / 4)) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ ≤ ((n : ℝ) + 1) * L ^ (-(min γ (1 - γ) + η / 4)) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hLp.le _) hn1
  -- case A: a cut vertex
  by_cases hA : ∃ w ∈ M.atoms, ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ w ∧ b ≠ w ∧
      ¬ (Degen.eraseAtoms M {w}).SameComponent a b
  · obtain ⟨w, hw, a, ha, b, hb, haw, hbw, hab⟩ := hA
    refine splitBound_mono (case_cut hLp j1 j8 hsz hM e hw ha hb haw hbw hab _) ?_ le_rfl
    rw [hn]
    have : K1 * Real.log L ^ B1 * ((n : ℝ) + 1) * (L ^ (-(3 / 5 * min γ (1 - γ))) * L ^ (-(3 / 5 * min γ (1 - γ)))) =
        (K1 * Real.log L ^ B1) * (((n : ℝ) + 1) * L ^ (-(3 / 5 * min γ (1 - γ)) + -(3 / 5 * min γ (1 - γ)))) := by
      rw [Real.rpow_add hLp]; ring
    rw [this]
    exact absorb hL1 k1 hn0 (by linarith)
  push Not at hA
  -- case B: a bridge of `𝕄 ∖ ℓ`
  by_cases hB : ∃ S ⊆ M.atoms, (crossDarts (MoleProp.eraseBond M e) S).card = 1
  · obtain ⟨S, hS, h1⟩ := hB
    refine splitBound_mono (case_bridge hLp j2 j8 hsz hM e hS h1 _) le_rfl ?_
    rw [← Real.rpow_add hLp]
    exact absorb' hL1 k2 hn1 (by linarith)
  push Not at hB
  -- case II: a bi-bridge
  by_cases hII : ∃ S ⊆ M.atoms, ∃ a ∈ S, ∃ b ∈ M.atoms, b ∉ S ∧ (crossDarts M S).card = 2
  · refine splitBound_mono (case_bibridge hLp j3 j4 j8 hsz hM e hA hB hII) ?_ ?_
    · rw [hn]
      have : K3 * Real.log L ^ B3 * ((n : ℝ) + 1) * L ^ min γ (1 - γ) *
          (L ^ (-(3 / 5 * min γ (1 - γ))) * L ^ (-(3 / 5 * min γ (1 - γ)))) =
          (K3 * Real.log L ^ B3) * (((n : ℝ) + 1) *
            L ^ (min γ (1 - γ) + (-(3 / 5 * min γ (1 - γ)) + -(3 / 5 * min γ (1 - γ))))) := by
        rw [Real.rpow_add hLp, Real.rpow_add hLp]; ring
      rw [this]
      exact absorb hL1 k3 hn0 (by linarith)
    · rw [← Real.rpow_add hLp]
      exact absorb' hL1 k4 hn1 (by linarith)
  push Not at hII
  -- case I: a double bond at an end of `ℓ`
  by_cases hI : ∃ w, M.bondsBetween (M.atom e) w = 2 ∨ M.bondsBetween (M.atom (M.mate e)) w = 2
  · refine splitBound_mono (case_pair hLp j5 j9 hsz hM e hII hI _) le_rfl ?_
    rw [mul_assoc, ← Real.rpow_add hLp]
    exact absorb' hL1 k5 hn1 (by linarith)
  push Not at hI
  -- cases III/IV: a double bond away from `ℓ`
  push Not at hs
  obtain ⟨v₁, v₂, hne, hlt⟩ := hs
  have hbb : M.bondsBetween v₁ v₂ = 2 := by have := hM.le2 v₁ v₂; omega
  have hv₂ : v₂ ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := v₁) (by omega)
  have hv₁ : v₁ ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := v₂) (by rw [bondsBetween_symm]; omega)
  have hp1 : M.atom e ≠ v₁ := fun h => (hI v₂).1 (by rw [h]; exact hbb)
  have hp2 : M.atom e ≠ v₂ := fun h => (hI v₁).1 (by rw [h, bondsBetween_symm]; exact hbb)
  have hq1 : M.atom (M.mate e) ≠ v₁ := fun h => (hI v₂).2 (by rw [h]; exact hbb)
  have hq2 : M.atom (M.mate e) ≠ v₂ := fun h => (hI v₁).2 (by rw [h, bondsBetween_symm]; exact hbb)
  have he : M.ends e ≠ s(v₁, v₂) := sym2_ne_of_left hp1 hp2
  have h4 := hM.four_le_card (M.atom_mem e)
  have hcore := merge_isCore hM hv₁ hv₂ hne hbb h4 hII
    (merge_not_T hv₁ hne hp1 hp2 (M.atom_mem e) (fun w => (hI w).1))
  have hcard := Merge.card_atoms (M := M) (hv₁ := hv₁) (hne := hne) hv₂
  have IH := ih (n - 1) (by omega) (mergePair M v₁ v₂ hv₁ hne) (by omega) (by
    have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    exact this.trans hszn) hcore ⟨e, he⟩
  have hcast : (((n - 1 : ℕ) : ℝ) + 1) = n := by rw [Nat.cast_sub (by omega)]; ring
  rw [hcast] at IH
  have hε₁ : 0 ≤ (n : ℝ) * L ^ (-(η / 4)) := mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg hLp.le _)
  have h6 : 6 ≤ M.atoms.card := six_le_card hM (M.atom_mem e) (M.atom_mem (M.mate e)) hv₁ hv₂ (hM.loop e) hne hp1 hp2
    hq1 hq2 hbb (fun w => (hI w).1) (fun w => (hI w).2)
  have hgood1 := goodCell_merge_core hM hv₁ hv₂ hne h6
  have hgood2 := goodCell_merge_erase hM e hv₁ hne hp1 hp2
  have hmain := case_merge hLp hlog j6 j7 j11 hM e hII hv₁ hv₂ hne hbb hp1 hp2 hq1 hq2 he hK6 hK7 hε₁ hgood1 hgood2 IH
  -- the two constants
  have hc1 : K6 * Real.log L ^ B6 * L ^ (-(min γ (1 - γ) - d * η)) ≤ 1 * L ^ (-(η / 4)) :=
    absorb' hL1 k6 le_rfl (by linarith)
  have hc2 : K7 * Real.log L ^ B7 * L ^ (-(η / 2)) ≤ 1 := by
    have h := absorb' hL1 k7 (le_refl (1 : ℝ)) (a := -(η / 2)) (b := 0) (by linarith)
    rwa [Real.rpow_zero, mul_one] at h
  refine splitBound_mono hmain ?_ ?_
  · calc K6 * Real.log L ^ B6 * L ^ (-(min γ (1 - γ) - d * η)) +
          K7 * Real.log L ^ B7 * L ^ (-(η / 2)) * ((n : ℝ) * L ^ (-(η / 4)))
        ≤ 1 * L ^ (-(η / 4)) + 1 * ((n : ℝ) * L ^ (-(η / 4))) :=
          add_le_add hc1 (mul_le_mul_of_nonneg_right hc2 hε₁)
      _ = ((n : ℝ) + 1) * L ^ (-(η / 4)) := by ring
  · have hε₂ : 0 ≤ (n : ℝ) * L ^ (-(min γ (1 - γ) + η / 4)) :=
      mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg hLp.le _)
    calc K7 * Real.log L ^ B7 * L ^ (-(η / 2)) * ((n : ℝ) * L ^ (-(min γ (1 - γ) + η / 4)))
        ≤ 1 * ((n : ℝ) * L ^ (-(min γ (1 - γ) + η / 4))) := mul_le_mul_of_nonneg_right hc2 hε₂
      _ ≤ ((n : ℝ) + 1) * L ^ (-(min γ (1 - γ) + η / 4)) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hLp.le _)

end WaveTurbulence.MoleProp4
