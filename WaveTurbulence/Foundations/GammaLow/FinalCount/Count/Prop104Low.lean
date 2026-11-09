/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Prop104TwoProved
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.Pair33
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.Merge
import Mathlib.Tactic

/-! # DH23 Proposition 10.4(2)′ with the low providers (packet L6-COUNT, item C; M2 §5)

Main's proof of Prop 10.4(2)′ (`G8R.CoreTheorem.core_split`, `G8R.Prop104Two.prop104_two`) uses `1/2 < γ` only to
discharge three of its named inputs, `PairGainInput`, `SmallGapPairInput`, `MergeInput`, each of the form
`1/2 < γ → …` (REF-M2 §2.6: `hγ12` occurs only in `(i5 hγ12)`, `(i6 hγ12)`, `(i7 hγ12 …)`). Their bodies
`PairGainAt`, `SmallGapPairAt`, `MergeAt` are unchanged; this module states them without the `1/2 < γ` premise and
proves them for every `γ ∈ (0,1)`, in particular at `0 < γ ≤ 1/2` (M2 §5.1–§5.3):
* pair gain (DH23 L1965, Lemma A.3(4)): `Count.pairGainAt_all` (`coupledTriple_bound` + the A.3(4) reparametrization);
* small-gap pair (DH23 L1975): main's `smallGapPairAt` (already stated for `γ ∈ (0,1)`);
* merge (DH23 L1977, Lemma A.3(1)): `Count.mergeAt_all` (the shell count at `γ ≤ 1/2`).
The other inputs (`BetaCut`, `BridgeSplit`, `BiBridge`, `BiBridgeEqual`, Prop 10.2 both statements) and G6's
Props 10.1, 10.3 are main's, for `γ ∈ (0,1)`.

* `PairGainInputLow`, `SmallGapPairInputLow`, `MergeInputLow`: main's `PairGainInput`, `SmallGapPairInput`,
  `MergeInput` without `1/2 < γ →`; providers `pairGainInputLow`, `smallGapPairInputLow`, `mergeInputLow`.
* `core_split_low`, `prop104_two_low`: main's `core_split`, `prop104_two` with these inputs and no `hγ12`
  (proofs copied verbatim otherwise).
* `Prop104TwoInputsLow`, `prop104TwoInputsLow_proved`, `prop104_two_proved_low`: main's `Prop104TwoInputs`,
  `prop104TwoInputs_proved`, `prop104_two_proved` for every `γ ∈ (0,1)`; the conclusion is main's verbatim.

Copied from main `FinalCount/G8R/CoreTheorem.lean`, `FinalCount/G8R/Prop104Two.lean`,
`FinalCount/Prop104TwoProved.lean` (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8

/-- **Pair gain without `1/2 < γ`** (DH23 L1965, Lemma A.3(4); M2 §5.1): main's `PairGainInput` minus its premise
`1 / 2 < γ`. -/
def PairGainInputLow (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    PairGainAt.{u, v} d L γ δ η C1 K B

/-- **Small-gap pair without `1/2 < γ`** (DH23 L1975; M2 §5.2): main's `SmallGapPairInput` minus its premise
`1 / 2 < γ`. -/
def SmallGapPairInputLow (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ K B R : ℝ, ∀ L ≥ R,
    SmallGapPairAt.{u, v} d L γ δ η C1 K B

/-- **Merge without `1/2 < γ`** (DH23 L1977, Lemma A.3(1); M2 §5.3): main's `MergeInput` minus its premise
`1 / 2 < γ` (the premises `0 < η`, `η ≤ γ₀/2` are kept). -/
def MergeInputLow (d : ℕ) (γ η : ℝ) : Prop :=
  0 < η → η ≤ min γ (1 - γ) / 2 → ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∃ K B R : ℝ, ∀ L ≥ R, MergeAt.{u, v} d L γ δ η C1 K B

/-- **The pair-gain provider, every `γ ∈ (0,1)`** (M2 §5.1). -/
theorem pairGainInputLow {d : ℕ} (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    PairGainInputLow.{u, v} d γ η :=
  ⟨1, le_rfl, fun C1 hC1 δ hδ => pairGainAt_all.{u, v} hd hγ hδ (by linarith) η⟩

/-- **The small-gap-pair provider, every `γ ∈ (0,1)`** (M2 §5.2; main's `smallGapPairAt`). -/
theorem smallGapPairInputLow {d : ℕ} (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hη : 0 ≤ η) :
    SmallGapPairInputLow.{u, v} d γ η :=
  ⟨1, le_rfl, fun C1 hC1 δ hδ => smallGapPairAt.{u, v} hd hγ hη hδ (by linarith)⟩

/-- **The merge provider, every `γ ∈ (0,1)`** (M2 §5.3). -/
theorem mergeInputLow {d : ℕ} (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) : MergeInputLow.{u, v} d γ η :=
  fun hη hηmax => ⟨1, le_rfl, fun C1 hC1 δ hδ => mergeAt_all.{u, v} hd hγ hη hηmax hδ (by linarith)⟩

/-- **The core of Prop 10.4(2)′, low providers** (main's `core_split` without `1/2 < γ`). -/
theorem core_split_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4)
    (i1 : BetaCutInput.{u, v} d γ η) (i2 : BridgeSplitInput.{u, v} d γ η) (i3 : BiBridgeInput.{u, v} d γ η)
    (i4 : BiBridgeEqualInput.{u, v} d γ η) (i5 : PairGainInputLow.{u, v} d γ η)
    (i6 : SmallGapPairInputLow.{u, v} d γ η) (i7 : MergeInputLow.{u, v} d γ η)
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
  have g5 := input_good (X := fun C1 δ L K B => PairGainAt.{u, v} d L γ δ η C1 K B) hθ i5
  have g6 := input_good_nonneg (X := fun C1 δ L K B => SmallGapPairAt.{u, v} d L γ δ η C1 K B) hθ
    (fun _ _ _ _ _ hL h => smallGapPairAt_mono hL h) i6
  have g7 := input_good_nonneg (X := fun C1 δ L K B => MergeAt.{u, v} d L γ δ η C1 K B) hθ
    (fun _ _ _ _ _ hL h => mergeAt_mono hL h) (i7 hη (by linarith))
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


/-- **The named inputs of Prop 10.4(2)′ with the low providers** at one LG parameter: main's `Prop104TwoInputs` with
`PairGainInputLow`, `SmallGapPairInputLow`, `MergeInputLow`. -/
def Prop104TwoInputsLow (d : ℕ) (γ η : ℝ) : Prop :=
  BetaCutInput.{u, v} d γ η ∧ BridgeSplitInput.{u, v} d γ η ∧ BiBridgeInput.{u, v} d γ η ∧
    BiBridgeEqualInput.{u, v} d γ η ∧ PairGainInputLow.{u, v} d γ η ∧ SmallGapPairInputLow.{u, v} d γ η ∧
    MergeInputLow.{u, v} d γ η ∧ Prop102Input.{u, v} d γ η ∧ Prop102SecondInput.{u, v} d γ η

/-- **DH23 Proposition 10.4(2)′, low providers** (main's `prop104_two` without `1/2 < γ`). -/
theorem prop104_two_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4)
    (hin0 : Prop104TwoInputsLow.{u, v} d γ η) (hin1 : Prop104TwoInputsLow.{u, v} d γ (η / 2))
    (hin2 : Prop104TwoInputsLow.{u, v} d γ (η / 4)) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
        (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
        (∀ a ∈ M.atoms, M.deg a = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
        (∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ w → b ≠ w →
          (Degen.eraseAtoms M {w}).SameComponent a b) →
        (∀ p q r s t u, 3 ≤ M.bondsBetween p q → 3 ≤ M.bondsBetween r s → 3 ≤ M.bondsBetween t u →
          s(p, q) = s(r, s) ∨ s(p, q) = s(t, u) ∨ s(r, s) = s(t, u)) → (∀ p q, M.bondsBetween p q ≤ 3) →
        (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        ¬ IsYExceptional M → ¬ YReachesSmallCell M →
        ∀ e : D, SplitBound M e d L γ δ η C1
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ((M.atoms.card + 1) * L ^ (-(η / 16))))
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ((M.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16)))) := by
  have hg : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith [hγ.2])
  have hηmax : η ≤ min γ (1 - γ) / 2 := by linarith
  have hη2 : 0 < η / 2 := by linarith
  have hη2max : η / 2 ≤ min γ (1 - γ) / 2 := by linarith
  have hη4 : 0 < η / 2 / 2 := by positivity
  have hdη : (0 : ℝ) ≤ d * η := by positivity
  obtain ⟨a0, b0, c0, e0, f0, g0, h0, p0, s0⟩ := hin0
  obtain ⟨a1, b1, c1, e1, f1, g1, h1, p1, s1⟩ := hin1
  have hin2' : Prop104TwoInputsLow.{u, v} d γ (η / 2 / 2) := by rw [show η / 2 / 2 = η / 4 by ring]; exact hin2
  obtain ⟨a2, b2, c2, e2, f2, g2, h2, p2, s2⟩ := hin2'
  obtain ⟨Cc0, hCc0, hc0⟩ := core_split_low d hd γ hγ η hη hη200 hηd a0 b0 c0 e0 f0 g0 h0 p0 s0
  obtain ⟨Cc1, hCc1, hc1⟩ := core_split_low d hd γ hγ (η / 2) hη2 (by linarith)
    (by rw [← mul_div_assoc]; linarith) a1 b1 c1 e1 f1 g1 h1 p1 s1
  obtain ⟨Cc2, hCc2, hc2⟩ := core_split_low d hd γ hγ (η / 2 / 2) hη4 (by linarith)
    (by rw [← mul_div_assoc, ← mul_div_assoc]; linarith) a2 b2 c2 e2 f2 g2 h2 p2 s2
  obtain ⟨Ct0, hCt0, ht0⟩ := split_transfer_Y2 d hd γ hγ η hη hηmax
  obtain ⟨Ct1, hCt1, ht1⟩ := split_transfer_Y2 d hd γ hγ (η / 2) hη2 hη2max
  obtain ⟨Cy0, hCy0, hy0⟩ := branch_y1c3 d hd γ hγ η hη hηmax p0 p1 s0
  obtain ⟨Cy1, hCy1, hy1⟩ := branch_y1c3 d hd γ hγ (η / 2) hη2 hη2max p1 p2 s1
  set Cs := max (max (max Cc0 Cc1) (max Cc2 Ct0)) (max (max Ct1 Cy0) Cy1) with hCs
  have k1 : Cc0 ≤ Cs := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have k2 : Cc1 ≤ Cs := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have k3 : Cc2 ≤ Cs := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have k4 : Ct0 ≤ Cs := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have k5 : Ct1 ≤ Cs := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have k6 : Cy0 ≤ Cs := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have k7 : Cy1 ≤ Cs := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨2 * Cs, by linarith, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R1, hR1⟩ := hc0 m C1 (by linarith) δ hδ
  obtain ⟨R2, hR2⟩ := hc1 m C1 (by linarith) δ hδ
  obtain ⟨R3, hR3⟩ := hc2 m C1 (by linarith) δ hδ
  obtain ⟨R4, hR4⟩ := ht0 C1 (by linarith) δ hδ
  obtain ⟨R5, hR5⟩ := ht1 C1 (by linarith) δ hδ
  obtain ⟨R6, hR6⟩ := hy0 m C1 (by linarith) δ hδ
  obtain ⟨R7, hR7⟩ := hy1 m C1 (by linarith) δ hδ
  refine ⟨max (max (max R1 R2) (max R3 R4)) (max (max R5 R6) (max R7 (Real.exp 1))), fun L hL => ?_⟩
  have l1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have l2 : R2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have l3 : R3 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have l4 : R4 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have l5 : R5 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have l6 : R6 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have l7 : R7 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hK := one_le_ylem2Const (L := L) hlog
  have hK0 : (0 : ℝ) ≤ 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 := zero_le_one.trans hK
  intro V D _ _ _ M hcap hloop h4 hconn hcut htri hle3 hsz hexc hns e
  classical
  -- Step 0 at the second level (LG parameter `η/2`): at most one triple bond
  have L1 : ∀ {D' : Type v} [Fintype D'] [DecidableEq D'] (N : Molecule V D'),
      (∀ a ∈ N.atoms, N.outdeg a ≤ 2 ∧ N.indeg a ≤ 2) → (∀ z, N.atom z ≠ N.atom (N.mate z)) →
      (∀ a ∈ N.atoms, N.deg a = 4) → (∀ a ∈ N.atoms, ∀ b ∈ N.atoms, N.SameComponent a b) →
      (∀ w ∈ N.atoms, ∀ a ∈ N.atoms, ∀ b ∈ N.atoms, a ≠ w → b ≠ w →
        (Degen.eraseAtoms N {w}).SameComponent a b) → (∀ p q, N.bondsBetween p q ≤ 3) →
      (∀ p q r s, 3 ≤ N.bondsBetween p q → 3 ≤ N.bondsBetween r s → s(p, q) = s(r, s)) →
      (N.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → ¬ YReachesQT N → ¬ YReachesSmallCell N → ∀ e₁ : D', SplitBound N e₁ d L γ δ (η / 2) C1
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 1 *
          ((N.atoms.card + 1) * L ^ (-(η / 16))))
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 1 *
          ((N.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16)))) := by
    intro D' _ _ N hcapN hloopN h4N hconnN hcutN hle3N honeN hszN hqtN hnsN e₁
    have hn0 : (0 : ℝ) ≤ N.atoms.card := Nat.cast_nonneg _
    by_cases hno : ∀ p q, N.bondsBetween p q ≤ 2
    · have hcore : IsCore N := ⟨hcapN, hloopN, h4N, hconnN, hno, fun hT =>
        hqtN (YReachesQT.done N (fun p q => by have := hno p q; omega) (Or.inr hT))⟩
      refine splitBound_mono (hR2 L l2 N hcore hszN e₁) ?_ ?_
      · calc ((N.atoms.card : ℝ) + 1) * L ^ (-(η / 2 / 4)) =
            _ ^ 0 * ((N.atoms.card + 1) * L ^ (-(η / 2 / 4))) := by ring
          _ ≤ _ := branch_cmp hK hL1 le_rfl hn0 (by linarith) (by norm_num)
      · calc ((N.atoms.card : ℝ) + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 4)) =
            _ ^ 0 * ((N.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 4))) := by ring
          _ ≤ _ := branch_cmp hK hL1 le_rfl hn0 (by linarith) (by norm_num)
    push Not at hno
    obtain ⟨p, q, hpq⟩ := hno
    have h3 : N.bondsBetween p q = 3 := by have := hle3N p q; omega
    have hpq' : p ≠ q := by rintro rfl; rw [bondsBetween_self_eq_zero hloopN] at h3; omega
    have hq : q ∈ N.atoms := mem_atoms_of_bondsBetween_pos (a := p) (by omega)
    have hp : p ∈ N.atoms := mem_atoms_of_bondsBetween_pos (a := q) (by rw [Degen.bondsBetween_comm]; omega)
    obtain ⟨C, hCa, hCb, hcomp⟩ := exists_complete hcapN hloopN hp hq hpq' h3
    rcases C.complete_4reg h4N hcomp with hE | ⟨E, hcompE⟩
    · -- (Y1) case 3: the first alternative
      obtain ⟨E⟩ := hE
      refine splitBound_mono (splitBound_of_first N e₁ (ε₂ := (110 * ((scaleSet L).card : ℝ) ^ 2 *
        (Real.log L ^ 2) ^ 6) ^ 1 * ((N.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16))))
        fun P hP => hR7 L l7 N hcapN hloopN h4N hconnN hcutN
          (fun _ _ _ _ _ _ h1 h2 _ => Or.inl (honeN _ _ _ _ h1 h2)) hle3N hszN C E P hP) ?_ le_rfl
      calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * L ^ (-(η / 2 / 3)) =
          _ ^ 1 * ((0 + 1) * L ^ (-(η / 2 / 3))) := by ring
        _ ≤ _ := branch_cmp hK hL1 hn0 le_rfl (by linarith) le_rfl
    · -- (Y2): the post molecule is core
      have hone : ∀ p' q', 3 ≤ N.bondsBetween p' q' → s(p', q') = s(C.a 0, C.b 0) := fun p' q' h => by
        rw [hCa, hCb]; exact honeN p' q' p q h (by omega)
      rcases E.post_noTriple hcapN hconnN h4N hle3N hone hcompE with hQ | hno2
      · exact absurd (YReachesQT.y2 N hcapN C E hcompE (YReachesQT.done _ (IsQ.bb_ne_three hQ) (Or.inl hQ))) hqtN
      have hpcore : IsCore (E.toTwoExit hcapN).post :=
        ⟨(E.toTwoExit hcapN).post_caps hcapN, (E.toTwoExit hcapN).post_loop hloopN, fun a ha => by
          rw [TwoExit.post_atoms] at ha
          rw [TwoExit.post_deg _ (mem_sdiff.mp ha).2]; exact h4N a (mem_sdiff.mp ha).1,
          (E.toTwoExit hcapN).post_connected hconnN, hno2, fun hT => hqtN (YReachesQT.y2 N hcapN C E hcompE
            (YReachesQT.done _ (fun p' q' => by have := hno2 p' q'; omega) (Or.inr hT)))⟩
      have hgood := E.good_of_not_small hcapN hconnN hcompE hnsN
      have hcard : ((E.toTwoExit hcapN).post.atoms.card : ℝ) ≤ N.atoms.card := by
        rw [TwoExit.post_atoms]; exact_mod_cast card_le_card sdiff_subset
      have hmain := hR5 L l5 N hcapN h4N hconnN C E hgood _ _ (fun e₂ => hR3 L l3 _ hpcore (hcard.trans hszN) e₂) e₁
      have hc0' : (0 : ℝ) ≤ (E.toTwoExit hcapN).post.atoms.card := Nat.cast_nonneg _
      refine splitBound_mono hmain ?_ ?_
      · calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 *
            (((E.toTwoExit hcapN).post.atoms.card + 1) * L ^ (-(η / 2 / 2 / 4))) =
            _ ^ 1 * (((E.toTwoExit hcapN).post.atoms.card + 1) * L ^ (-(η / 2 / 2 / 4))) := by ring
          _ ≤ _ := branch_cmp hK hL1 hcard hc0' (by linarith) le_rfl
      · calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 *
            (((E.toTwoExit hcapN).post.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 2 / 4))) =
            _ ^ 1 * (((E.toTwoExit hcapN).post.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 2 / 4))) := by ring
          _ ≤ _ := branch_cmp hK hL1 hcard hc0' (by linarith) le_rfl
  -- the first level
  have hn0 : (0 : ℝ) ≤ M.atoms.card := Nat.cast_nonneg _
  by_cases hno : ∀ p q, M.bondsBetween p q ≤ 2
  · have hcore : IsCore M := ⟨hcap, hloop, h4, hconn, hno, fun hT =>
      hexc (YReachesQT.done M (fun p q => by have := hno p q; omega) (Or.inr hT))⟩
    refine splitBound_mono (hR1 L l1 M hcore hsz e) ?_ ?_
    · calc ((M.atoms.card : ℝ) + 1) * L ^ (-(η / 4)) = _ ^ 0 * ((M.atoms.card + 1) * L ^ (-(η / 4))) := by ring
        _ ≤ _ := branch_cmp hK hL1 le_rfl hn0 (by linarith) (by norm_num)
    · calc ((M.atoms.card : ℝ) + 1) * L ^ (-(min γ (1 - γ) + η / 4)) =
          _ ^ 0 * ((M.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 4))) := by ring
        _ ≤ _ := branch_cmp hK hL1 le_rfl hn0 (by linarith) (by norm_num)
  push Not at hno
  obtain ⟨p, q, hpq⟩ := hno
  have h3 : M.bondsBetween p q = 3 := by have := hle3 p q; omega
  have hpq' : p ≠ q := by rintro rfl; rw [bondsBetween_self_eq_zero hloop] at h3; omega
  have hq : q ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := p) (by omega)
  have hp : p ∈ M.atoms := mem_atoms_of_bondsBetween_pos (a := q) (by rw [Degen.bondsBetween_comm]; omega)
  obtain ⟨C, _, _, hcomp⟩ := exists_complete hcap hloop hp hq hpq' h3
  rcases C.complete_4reg h4 hcomp with hE | ⟨E, hcompE⟩
  · obtain ⟨E⟩ := hE
    refine splitBound_mono (splitBound_of_first M e (ε₂ := (110 * ((scaleSet L).card : ℝ) ^ 2 *
      (Real.log L ^ 2) ^ 6) ^ 2 * ((M.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16))))
      fun P hP => hR6 L l6 M hcap hloop h4 hconn hcut htri hle3 hsz C E P hP) ?_ le_rfl
    calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * L ^ (-(η / 3)) =
        _ ^ 1 * ((0 + 1) * L ^ (-(η / 3))) := by ring
      _ ≤ _ := branch_cmp hK hL1 hn0 le_rfl (by linarith) (by norm_num)
  · rcases E.post_triples hcap hconn h4 hle3 htri hcompE with hQ | ⟨hle3', hone'⟩
    · exact absurd (YReachesQT.y2 M hcap C E hcompE (YReachesQT.done _ (IsQ.bb_ne_three hQ) (Or.inl hQ))) hexc
    have hcard : ((E.toTwoExit hcap).post.atoms.card : ℝ) ≤ M.atoms.card := by
      rw [TwoExit.post_atoms]; exact_mod_cast card_le_card sdiff_subset
    have hpost := L1 (E.toTwoExit hcap).post ((E.toTwoExit hcap).post_caps hcap) ((E.toTwoExit hcap).post_loop hloop)
      (fun a ha => by
        rw [TwoExit.post_atoms] at ha
        rw [TwoExit.post_deg _ (mem_sdiff.mp ha).2]; exact h4 a (mem_sdiff.mp ha).1)
      ((E.toTwoExit hcap).post_connected hconn) ((E.toTwoExit hcap).post_noCut hcut) hle3' hone' (hcard.trans hsz)
      (fun h => hexc (YReachesQT.y2 M hcap C E hcompE h)) (fun h => hns (YReachesSmallCell.y2 M hcap C E hcompE h))
    have hgood := E.good_of_not_small hcap hconn hcompE hns
    have hmain := hR4 L l4 M hcap h4 hconn C E hgood _ _ hpost e
    have hc0' : (0 : ℝ) ≤ (E.toTwoExit hcap).post.atoms.card := Nat.cast_nonneg _
    refine splitBound_mono hmain ?_ ?_
    · calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 *
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 1 *
            (((E.toTwoExit hcap).post.atoms.card + 1) * L ^ (-(η / 16)))) =
          _ ^ 2 * (((E.toTwoExit hcap).post.atoms.card + 1) * L ^ (-(η / 16))) := by ring
        _ ≤ _ := branch_cmp hK hL1 hcard hc0' le_rfl le_rfl
    · calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 *
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 1 *
            (((E.toTwoExit hcap).post.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16)))) =
          _ ^ 2 * (((E.toTwoExit hcap).post.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16))) := by ring
        _ ≤ _ := branch_cmp hK hL1 hcard hc0' le_rfl le_rfl


/-- **All inputs of Prop 10.4(2)′ with the low providers, every `γ ∈ (0,1)`**: main's `prop104TwoInputs_proved`. -/
theorem prop104TwoInputsLow_proved (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1 - γ)) (hηs : 4 * 1440061 * η ≤ 1) : Prop104TwoInputsLow.{u, v} d γ η :=
  ⟨betaCutInput d γ η, bridgeSplitInput d γ η, biBridgeInput d γ η hγ,
    bibridgeEqualInput d γ η, pairGainInputLow hd γ η hγ, smallGapPairInputLow hd γ η hγ hη.le,
    mergeInputLow hd γ η hγ,
    prop102InputSz d hd γ η hγ hη hηγ hηs,
    prop102SecondInputSz d hd γ η hγ hη hηγ hηs⟩

/-- **DH23 Prop 10.4(2)′ for every `γ ∈ (0,1)`, all counting inputs proved** (in particular at `0 < γ ≤ 1/2`; M2 §5.4):
main's `prop104_two_proved` with the low providers. The conclusion is main's verbatim. -/
theorem prop104_two_proved_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
        (∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) → (∀ z, M.atom z ≠ M.atom (M.mate z)) →
        (∀ a ∈ M.atoms, M.deg a = 4) → (∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b) →
        (∀ w ∈ M.atoms, ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, a ≠ w → b ≠ w →
          (Degen.eraseAtoms M {w}).SameComponent a b) →
        (∀ p q r s t u, 3 ≤ M.bondsBetween p q → 3 ≤ M.bondsBetween r s → 3 ≤ M.bondsBetween t u →
          s(p, q) = s(r, s) ∨ s(p, q) = s(t, u) ∨ s(r, s) = s(t, u)) → (∀ p q, M.bondsBetween p q ≤ 3) →
        (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        ¬ IsYExceptional M → ¬ YReachesSmallCell M →
        ∀ e : D, SplitBound M e d L γ δ η C1
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ((M.atoms.card + 1) * L ^ (-(η / 16))))
          ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
            ((M.atoms.card + 1) * L ^ (-(min γ (1 - γ) + η / 16)))) := by
  have hg : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith [hγ.2])
  exact prop104_two_low.{u, v} d hd γ hγ η hη hη200 hηd
    (prop104TwoInputsLow_proved d hd γ η hγ hη (by linarith) hηs)
    (prop104TwoInputsLow_proved d hd γ (η / 2) hγ (by linarith) (by linarith) (by linarith))
    (prop104TwoInputsLow_proved d hd γ (η / 4) hγ (by linarith) (by linarith) (by linarith))

end WaveTurbulence.GammaLow.FinalCount.Count
