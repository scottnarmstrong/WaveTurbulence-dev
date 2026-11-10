/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Part2Num
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Part2Op
public import WaveTurbulence.Foundations.XChain.FlowerDraft.Obligations

/-!
# X3 Part2: O-X3-PART2 discharged; B1.3 `fixedpoint` from the gates

**Statement.**
1. (`part2Body_of_X2`) `X2Body Pm P` (the moments of `flowerest1`) gives `Part2Body P`. This holds for
   `Pm ≥ 100 (d+1)²`, `d ≥ 3`, and `L` beyond the threshold of `exists_L0_part2`. The excluded data set is
   `part2Set`, the intersection of the Part 2 events over the three kinds and both `ζ`. It is:
   - measurable;
   - stable under cubic phases;
   - of probability `≤ 6 · e^{−4N}/12 = e^{−4N}/2` on `F_p`.

   Outside it, `‖𝒴‖, ‖𝒲‖ ≤ 1/2` (threshold `B = 1/(4·2^{Λ/2} S_L)`) and `‖𝒳‖ ≤ 1 + e^{2N}/2 ≤ e^{2N}`
   (threshold `B = e^{2N}/(4·2^{Λ/2} S_L)`) on `Z`.
2. (`part2_of_X2`) `WTPrefixP X2Body → WTPrefix Part2Body`, choosing `Pm = max(P₀, 100(d+1)²)`, which is free
   in `WTPrefixP`.
3. (`fixedpoint_of_gates`) **B1.3 `fixedpoint`** (snapshot 5) follows from:
   - B1.12 (snapshot 6), B1.2 `layergarden`, B1.5 `wkeTaylor`;
   - the named obligations O-X2-EXP and O-X3-CPL.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI FTree
open scoped ENNReal

universe u

/-- **The Part 2 data set**: the events of the three kinds, both `ζ`. -/
def part2Set (P : WTParams) (Pm p : ℕ) : Set ((Fin P.d → ℤ) → ℂ) :=
  (⋂ ζ : ℤˣ, part2Event P.L P.γ P.δ p (P.N (p + 1)) .X ζ (par2 P Pm p .X)) ∩
    (⋂ ζ : ℤˣ, part2Event P.L P.γ P.δ p (P.N (p + 1)) .Y ζ (par2 P Pm p .Y)) ∩
      (⋂ ζ : ℤˣ, part2Event P.L P.γ P.δ p (P.N (p + 1)) .W ζ (par2 P Pm p .W))

theorem mem_part2Set {P : WTParams} {Pm p : ℕ} {b : (Fin P.d → ℤ) → ℂ} (h : b ∈ part2Set P Pm p)
    (kind : FlowerKind) (ζ : ℤˣ) : b ∈ part2Event P.L P.γ P.δ p (P.N (p + 1)) kind ζ (par2 P Pm p kind) := by
  cases kind with
  | X => exact mem_iInter.1 h.1.1 ζ
  | Y => exact mem_iInter.1 h.1.2 ζ
  | W => exact mem_iInter.1 h.2 ζ

/-- The probability for one kind: both `ζ`. -/
theorem prob_not_iInter_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Set Ω) {α : Type*}
    (a : Ω → α) (E : ℤˣ → Set α) {x : ℝ} (h : ∀ ζ, μ (F ∩ {ω | a ω ∉ E ζ}) ≤ ENNReal.ofReal x) :
    μ (F ∩ {ω | a ω ∉ ⋂ ζ, E ζ}) ≤ ENNReal.ofReal (2 * x) := by
  have hsub : F ∩ {ω | a ω ∉ ⋂ ζ, E ζ} ⊆ ⋃ ζ, F ∩ {ω | a ω ∉ E ζ} := by
    rintro ω ⟨hω, hn⟩
    rw [mem_ofPred_eq, mem_iInter, not_forall] at hn
    obtain ⟨ζ, hζ⟩ := hn
    exact mem_iUnion.2 ⟨ζ, hω, hζ⟩
  calc μ (F ∩ {ω | a ω ∉ ⋂ ζ, E ζ}) ≤ ∑' ζ, μ (F ∩ {ω | a ω ∉ E ζ}) :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' _ζ : ℤˣ, ENNReal.ofReal x := ENNReal.tsum_le_tsum h
    _ = ENNReal.ofReal (2 * x) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_units_int, nsmul_eq_mul,
          ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- **O-X3-PART2 from `X2Body`.** -/
theorem part2Body_of_X2 {Pm : ℕ} {P : WTParams} (hX2 : X2Body.{u} Pm P) (hPm : 100 * ((P.d : ℝ) + 1) ^ 2 ≤ Pm)
    (hd : 3 ≤ P.d) (hL : Real.exp 1 ≤ P.L)
    (hnum : ∀ p, p < P.D → ∀ kind : FlowerKind,
      2 * (cA P Pm p kind * (3 * P.L) ^ P.d * latSum P.d P.L) +
          4 * (cB P Pm p kind * latSum P.d P.L * KB P Pm (P.N (p + 1)) kind) ≤
        Real.exp (-(4 * P.N (p + 1) : ℝ)) / 12) :
    Part2Body.{u} P := by
  intro Ω _ μ _ g hg p hp a Fev R E Et hA
  have hL1 : 1 ≤ P.L := le_trans (Real.one_le_exp zero_le_one) hL
  have hL0 : 0 < P.L := by linarith
  have hd1 : 1 ≤ P.d := by omega
  have hd0 : 0 < P.d := by omega
  have hPm1 : 1 ≤ Pm := by
    have h0 : (1 : ℝ) ≤ 100 * ((P.d : ℝ) + 1) ^ 2 := by
      have : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
      nlinarith
    have : (1 : ℝ) ≤ Pm := h0.trans hPm
    exact_mod_cast this
  obtain ⟨hΛ40, -⟩ := Lambda_ge P hp hd1
  set N := P.N (p + 1)
  set Λ : ℝ := 5 / 4 * (P.Lambda (p + 1) : ℝ) with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  have hΛd : (P.d : ℝ) + 1 ≤ Λ := by
    have : (40 * P.d : ℝ) ≤ (P.Lambda (p + 1) : ℝ) := by exact_mod_cast hΛ40
    have : (1 : ℝ) ≤ P.d := by exact_mod_cast hd1
    linarith
  refine ⟨part2Set P Pm p, ?_, ?_, ?_, ?_⟩
  · -- measurable
    exact ((MeasurableSet.iInter fun ζ => measurableSet_part2Event _ _ _ _ _ _ ζ _).inter
      (MeasurableSet.iInter fun ζ => measurableSet_part2Event _ _ _ _ _ _ ζ _)).inter
      (MeasurableSet.iInter fun ζ => measurableSet_part2Event _ _ _ _ _ _ ζ _)
  · -- phase stability
    intro φ hφ b hb _
    refine ⟨⟨mem_iInter.2 fun ζ => ?_, mem_iInter.2 fun ζ => ?_⟩, mem_iInter.2 fun ζ => ?_⟩ <;>
      exact mul_phase_mem_part2Event _ _ _ _ _ _ _ _ hφ (mem_part2Set hb _ ζ)
  · -- the probability
    have hk : ∀ kind : FlowerKind, ∀ ζ : ℤˣ,
        μ (Fev p ∩ {ω | a ω p ∉ part2Event P.L P.γ P.δ p N kind ζ (par2 P Pm p kind)}) ≤
          ENNReal.ofReal (Real.exp (-(4 * N : ℝ)) / 12) := by
      intro kind ζ
      have hπ := par2_valid P Pm p kind hPm1 hL1
      refine (prob_not_part2Event P Pm p kind ζ (par2 P Pm p kind) hX2 rfl hπ (par2_B_pos P Pm p kind hL1)
        (par2_v_pos P Pm p kind) hL1 μ hg hp hA).trans ?_
      refine (probSum_le_tot P Pm p kind ζ hPm hPm1 hd1 hΛ40 hL1).trans ?_
      exact ENNReal.ofReal_le_ofReal (hnum p hp kind)
    have he : 0 ≤ Real.exp (-(4 * N : ℝ)) / 12 := by positivity
    have hsub : Fev p ∩ {ω | a ω p ∉ part2Set P Pm p} ⊆
        (Fev p ∩ {ω | a ω p ∉ ⋂ ζ, part2Event P.L P.γ P.δ p N .X ζ (par2 P Pm p .X)}) ∪
        (Fev p ∩ {ω | a ω p ∉ ⋂ ζ, part2Event P.L P.γ P.δ p N .Y ζ (par2 P Pm p .Y)}) ∪
        (Fev p ∩ {ω | a ω p ∉ ⋂ ζ, part2Event P.L P.γ P.δ p N .W ζ (par2 P Pm p .W)}) := by
      rintro ω ⟨hω, hn⟩
      simp only [part2Set, mem_ofPred_eq, mem_inter_iff, not_and_or] at hn
      rcases hn with (h | h) | h
      · exact Or.inl (Or.inl ⟨hω, h⟩)
      · exact Or.inl (Or.inr ⟨hω, h⟩)
      · exact Or.inr ⟨hω, h⟩
    calc μ (Fev p ∩ {ω | a ω p ∉ part2Set P Pm p})
        ≤ μ (Fev p ∩ {ω | a ω p ∉ ⋂ ζ, part2Event P.L P.γ P.δ p N .X ζ (par2 P Pm p .X)}) +
          μ (Fev p ∩ {ω | a ω p ∉ ⋂ ζ, part2Event P.L P.γ P.δ p N .Y ζ (par2 P Pm p .Y)}) +
          μ (Fev p ∩ {ω | a ω p ∉ ⋂ ζ, part2Event P.L P.γ P.δ p N .W ζ (par2 P Pm p .W)}) :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _))
      _ ≤ ENNReal.ofReal (2 * (Real.exp (-(4 * N : ℝ)) / 12)) +
          ENNReal.ofReal (2 * (Real.exp (-(4 * N : ℝ)) / 12)) +
          ENNReal.ofReal (2 * (Real.exp (-(4 * N : ℝ)) / 12)) := by
          gcongr
          · exact prob_not_iInter_le μ _ (fun ω => a ω p) _ (hk .X)
          · exact prob_not_iInter_le μ _ (fun ω => a ω p) _ (hk .Y)
          · exact prob_not_iInter_le μ _ (fun ω => a ω p) _ (hk .W)
      _ = ENNReal.ofReal (Real.exp (-(4 * N : ℝ)) / 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  · -- the operator bounds
    intro b hb hbs c hc
    have hgood : Good p c := good_of_mem_ZSpace P.L hL1 hΛd hc
    have hA : ∀ kind : FlowerKind, Λ + (P.d + 1) ≤ (par2 P Pm p kind).A := fun kind => by
      show Λ + (P.d + 1) ≤ 5 / 4 * (P.Lambda (p + 1) : ℝ) + P.d + 1
      rw [hΛdef]; linarith
    have hS := latSum_pos (d := P.d) hL1
    have hop : ∀ kind : FlowerKind, ∀ {K : ℤˣ → ℝ → ℝ → (Fin P.d → ℤ) → (Fin P.d → ℤ) → ℂ},
        (∀ ζ t s k k', (p : ℝ) < s → s < t → t ≤ p + 1 →
          K ζ t s k k' = randFlowerKernel P.L P.γ P.δ p N b kind .plain none none none ζ t s k k') →
        ZNorm P.L Λ (kernelOp p K c) ≤
          ENNReal.ofReal (kindBeta N kind / 2) * ZNorm P.L Λ c := by
      intro kind K hK
      refine (ZNorm_kernelOp_le_of_event P.L P.γ P.δ p N kind (par2 P Pm p kind)
        (par2_valid P Pm p kind hPm1 hL1) hL1 hd0 hΛ0 (hA kind) hbs (fun ζ => mem_part2Set hb kind ζ) hK hc).trans
        (le_of_eq ?_)
      congr 2
      show 2 * 2 ^ (Λ / 2) * (kindBeta N kind / (4 * 2 ^ (5 / 4 * (P.Lambda (p + 1) : ℝ) / 2) *
        latSum P.d P.L)) * latSum P.d P.L = kindBeta N kind / 2
      rw [← hΛdef]
      field_simp
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [Yop_eq_kernelOp P.L P.γ P.δ p N hbs hgood]
      refine (hop .Y fun ζ t s k k' h1 h2 h3 => Yker_eq_rand P.L P.γ P.δ p N b ζ h1 h2 h3 k k').trans
        (le_of_eq ?_)
      simp [kindBeta]
    · rw [Wop_eq_kernelOp P.L P.γ P.δ p N hbs hgood]
      refine (hop .W fun ζ t s k k' h1 h2 h3 => Wker_eq_rand P.L P.γ P.δ p N b ζ h1 h2 h3 k k').trans
        (le_of_eq ?_)
      simp [kindBeta]
    · rw [Xop_eq_kernelOp P.L P.γ P.δ p N hbs hgood]
      have hX := hop .X fun ζ t s k k' h1 h2 h3 => Xker_eq_rand P.L P.γ P.δ p N b ζ h1 h2 h3 k k'
      have hN1 : (1 : ℝ) ≤ N := by
        have hx : 1 ≤ Real.log P.L := by
          rw [← Real.exp_le_exp, Real.exp_log hL0]
          exact hL
        have h1 : 1 ≤ P.Rdown 0 := WTParams.one_le_Rdown_zero P hx
        exact_mod_cast h1.trans (WTParams.Rdown_zero_le_N P hd1 h1 (p + 1))
      have he2 : 1 + Real.exp (2 * N) / 2 ≤ Real.exp (2 * N) := by
        have := Real.add_one_le_exp (2 * (N : ℝ))
        linarith
      calc ZNorm P.L Λ (c + kernelOp p (Xker P.L P.γ P.δ p N b) c)
          ≤ ZNorm P.L Λ c + ZNorm P.L Λ (kernelOp p (Xker P.L P.γ P.δ p N b) c) := ZNorm_add_le P.L Λ _ _
        _ ≤ ZNorm P.L Λ c + ENNReal.ofReal (Real.exp (2 * N) / 2) * ZNorm P.L Λ c := by
            gcongr
            exact hX
        _ = ENNReal.ofReal (1 + Real.exp (2 * N) / 2) * ZNorm P.L Λ c := by
            rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, add_mul, one_mul]
        _ ≤ ENNReal.ofReal (Real.exp (2 * N)) * ZNorm P.L Λ c := by
            gcongr

end WaveTurbulence.Fixedpt
