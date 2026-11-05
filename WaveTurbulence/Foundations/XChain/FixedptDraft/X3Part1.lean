/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Cov
public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3SupProb

/-!
# X3 Part 1: (fixedest1), (fixedest2) (T L2307–L2315)

`part1_prob`: on `F = Fev p`, given the couple moments of B1.12 clause (2) (`CplMomBody`):
- `𝔼_F |a^tr_n(t)|² ≤ ⟨n⟩^{-4Λ} L²`, `𝔼_F |∂_t a^tr_n(t)|² ≤ ⟨n⟩^{-4Λ} L^{2+100d}`;
- `𝔼_F |ℒ₀|²`, `𝔼_F |∂_tℒ₀|²`: the same with an extra factor `e^{-100N}`.

The probability that clause (1) or (2) of `fixedpoint` fails is at most
`(2L²(1+L^{100d})/e^{6N} + 2L²(1+L^{100d})e^{-100N}/e^{-40N}) · T`, `T = ∑_n ⟨n/L⟩^{-(d+1)}`.

The proof, for each mode `n`:
- Sobolev in `t` and Chebyshev (`prob_sup_le`);
- the union over `n` costs `∑_n ⟨n⟩^{-Λ} ≤ T`.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI
open scoped ENNReal

variable (L γ δ : ℝ) {d : ℕ}

/-! ## The fundamental theorem of calculus for the couple quantities -/

section FTC

theorem intervalIntegrable_L0Dt_p (p Ntr : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (t : ℝ)
    (n : Fin d → ℤ) : IntervalIntegrable (fun s => L0Dt L γ δ p Ntr b s n) volume p t := by
  unfold L0Dt
  have h := IntervalIntegrable.sum (μ := volume) (a := (p : ℝ)) (b := t)
    ((Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
      (fun x => slotCountB x = 0 ∧ (0 = 0 → Ntr ≤ slotOrder x)))
    (f := fun x s => aNonlin L γ δ 1 s (slotValAt L γ δ p Ntr b x.1 s)
      (fun m => (starRingEnd ℂ) (slotValAt L γ δ p Ntr b x.2.1 s m)) (slotValAt L γ δ p Ntr b x.2.2 s) n)
    fun x hx => by
      obtain ⟨h1, h2, h3⟩ := slots_ne_none (Finset.mem_filter.1 hx).2.1
      obtain ⟨N₁, e1⟩ := Option.ne_none_iff_exists'.1 h1
      obtain ⟨N₂, e2⟩ := Option.ne_none_iff_exists'.1 h2
      obtain ⟨N₃, e3⟩ := Option.ne_none_iff_exists'.1 h3
      simp only [e1, e2, e3, slotValAt]
      exact intervalIntegrable_treeTermN_triple L γ δ p N₁ N₂ N₃ hb t n
  rwa [Finset.sum_fn] at h

theorem intervalIntegrable_L0Dt (p Ntr : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (t₀ t : ℝ)
    (n : Fin d → ℤ) : IntervalIntegrable (fun s => L0Dt L γ δ p Ntr b s n) volume t₀ t :=
  (intervalIntegrable_L0Dt_p L γ δ p Ntr hb t₀ n).symm.trans (intervalIntegrable_L0Dt_p L γ δ p Ntr hb t n)

theorem L0_sub (hL : 0 < L) (p Ntr : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖)
    (b₀ : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (t t₀ : ℝ) (n : Fin d → ℤ) :
    Lop L γ δ p Ntr b 0 b₀ t n - Lop L γ δ p Ntr b 0 b₀ t₀ n = ∫ s in t₀..t, L0Dt L γ δ p Ntr b s n := by
  rw [L0_eq L γ δ hL p Ntr hb b₀ t n, L0_eq L γ δ hL p Ntr hb b₀ t₀ n,
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_L0Dt_p L γ δ p Ntr hb t n)
      (intervalIntegrable_L0Dt_p L γ δ p Ntr hb t₀ n)]

theorem intervalIntegrable_aTrDt (p Ntr : ℕ) {b : (Fin d → ℤ) → ℂ} (hb : Summable fun k => ‖b k‖) (t₀ t : ℝ)
    (n : Fin d → ℤ) : IntervalIntegrable (fun s => aTrDt L γ δ p Ntr b s n) volume t₀ t := by
  simp only [aTrDt_eq_sum]
  have h := IntervalIntegrable.sum (μ := volume) (a := t₀) (b := t) (Finset.range (Ntr + 1))
    (f := fun N s => ∑ T ∈ treesOfOrder N, treeTermDt L γ δ p T b s n) fun N _ => by
      have h' := IntervalIntegrable.sum (μ := volume) (a := t₀) (b := t) (treesOfOrder N)
        (f := fun T s => treeTermDt L γ δ p T b s n)
        (fun T _ => intervalIntegrable_treeTermDt L γ δ p hb T t₀ t n)
      rwa [Finset.sum_fn] at h'
  rwa [Finset.sum_fn] at h

end FTC

/-! ## Part 1 -/

section Part1

/-- **The good set of Part 1**: clauses (1), (2) of `fixedpoint`, as a set of data `a(p)`. -/
def Good1 (P : WTParams) (p : ℕ) : Set ((Fin P.d → ℤ) → ℂ) :=
  {b | (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n, ‖aTr P.L P.γ P.δ p (P.N (p + 1)) b t n‖ ≤
        jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) * Real.exp (3 * (P.N (p + 1) : ℝ))) ∧
    (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n, ‖Lop P.L P.γ P.δ p (P.N (p + 1)) b 0 (fun _ _ => 0) t n‖ ≤
        jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) * Real.exp (-(20 * P.N (p + 1) : ℝ)))}

/-- The bound of Part 1. -/
noncomputable def part1Bound (P : WTParams) (p : ℕ) : ℝ :=
  (2 * P.L ^ 2 * (1 + P.L ^ (100 * P.d : ℝ)) / Real.exp (3 * (P.N (p + 1) : ℝ)) ^ 2 +
    2 * (P.L ^ 2 * Real.exp (-(100 * P.N (p + 1) : ℝ))) * (1 + P.L ^ (100 * P.d : ℝ)) /
      Real.exp (-(20 * P.N (p + 1) : ℝ)) ^ 2) * latSum P.d P.L

/-- `(2c + 2c')/B² = 2A(1+M)/E² · J^{-Λ}` for `c = J^{-4Λ}A`, `c' = J^{-4Λ}AM`, `B = J^{-(3/2)Λ}E`. -/
theorem ratio_eq {J A M E Λ c c' : ℝ} (hJ : 0 < J) (hE : 0 < E) (hc : c = J ^ (-(4 * Λ)) * A)
    (hc' : c' = J ^ (-(4 * Λ)) * A * M) :
    (2 * c + 2 * c') / (J ^ (-(3 / 2 * Λ)) * E) ^ 2 = 2 * A * (1 + M) / E ^ 2 * J ^ (-Λ) := by
  have h1 : J ^ (-(4 * Λ)) = J ^ (-Λ) * (J ^ (-(3 / 2 * Λ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hJ.le, ← Real.rpow_add hJ]
    congr 1
    push_cast
    ring
  have hJ' : 0 < J ^ (-(3 / 2 * Λ)) := Real.rpow_pos_of_pos hJ _
  rw [hc, hc', h1]
  field_simp

variable (P : WTParams) (p : ℕ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
  {F : Set Ω} (hF : MeasurableSet F) {aP : Ω → (Fin P.d → ℤ) → ℂ} (haP : ∀ k, Measurable fun ω => aP ω k)
  (hsum : ∀ ω ∈ F, Summable fun k => ‖aP ω k‖)
  (hmom : ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ (n : Fin P.d → ℤ) (v : CplVar),
    Integrable (fun ω => ‖cplRand P (aP ω) p v t n‖ ^ 2) (μ.restrict F) ∧
    ∫ ω in F, ‖cplRand P (aP ω) p v t n‖ ^ 2 ∂μ ≤ cplBound P p n v)

omit [IsFiniteMeasure μ] in
include hF hsum hmom in
/-- The moments of `sumMod ∘ a(p)` (equal to `a(p)` on `F`). -/
theorem mom_sumMod (t : ℝ) (ht : t ∈ Ioo (p : ℝ) (p + 1)) (n : Fin P.d → ℤ) (v : CplVar) :
    Integrable (fun ω => ‖cplRand P (sumMod (aP ω)) p v t n‖ ^ 2) (μ.restrict F) ∧
    ∫ ω in F, ‖cplRand P (sumMod (aP ω)) p v t n‖ ^ 2 ∂μ ≤ cplBound P p n v := by
  have heq : ∀ ω ∈ F, ‖cplRand P (sumMod (aP ω)) p v t n‖ ^ 2 = ‖cplRand P (aP ω) p v t n‖ ^ 2 :=
    fun ω hω => by rw [sumMod_of_summable (hsum ω hω)]
  refine ⟨(hmom t ht n v).1.congr ((ae_restrict_iff' hF).2 (ae_of_all _ fun ω hω => (heq ω hω).symm)), ?_⟩
  rw [setIntegral_congr_fun hF heq]
  exact (hmom t ht n v).2

omit [IsFiniteMeasure μ] in
include haP in
theorem stronglyMeasurable_sumMod_fst {β : Type*} [MeasurableSpace β] (k : Fin P.d → ℤ) :
    StronglyMeasurable fun z : Ω × β => sumMod (aP z.1) k :=
  stronglyMeasurable_sumMod (fun k => ((haP k).comp measurable_fst).stronglyMeasurable) k

omit [IsFiniteMeasure μ] in
include haP in
theorem stronglyMeasurable_sumMod_fst_fst {β β' : Type*} [MeasurableSpace β] [MeasurableSpace β'] (k : Fin P.d → ℤ) :
    StronglyMeasurable fun z : (Ω × β) × β' => sumMod (aP z.1.1) k :=
  stronglyMeasurable_sumMod (fun k => ((haP k).comp (measurable_fst.comp measurable_fst)).stronglyMeasurable) k

include hF haP hsum hmom in
/-- **One mode of `a^tr`.** -/
theorem prob_aTr_mode (hL1 : 1 ≤ P.L) (n : Fin P.d → ℤ) :
    μ (F ∩ {ω | ∃ t ∈ Icc (p : ℝ) (p + 1),
        jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) * Real.exp (3 * (P.N (p + 1) : ℝ)) <
          ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP ω)) t n‖}) ≤
      ENNReal.ofReal ((2 * cplBound P p n .aTr + 2 * cplBound P p n .aTrDt) /
        (jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) * Real.exp (3 * (P.N (p + 1) : ℝ))) ^ 2) := by
  have hJ := jbr_pos'' (latticePoint P.L n)
  refine prob_sup_le μ hF (f := fun ω t => aTr P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP ω)) t n)
    (g := fun ω t => aTrDt P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP ω)) t n) ?_ ?_ ?_ ?_ ?_ ?_
    (mul_pos (Real.rpow_pos_of_pos hJ _) (Real.exp_pos _)) ?_ ?_
  · exact stronglyMeasurable_aTr' P.L P.γ P.δ (stronglyMeasurable_sumMod_fst P haP)
      (fun z => summable_sumMod _) measurable_snd p _ n
  · exact stronglyMeasurable_aTrDt' P.L P.γ P.δ (stronglyMeasurable_sumMod_fst P haP)
      (fun z => summable_sumMod _) measurable_snd p _ n
  · intro ω _ t ht t₀ ht₀
    exact aTr_sub P.L P.γ P.δ p _ (summable_sumMod _) ht.1 ht₀.1 n
  · intro ω _
    exact intervalIntegrable_aTrDt P.L P.γ P.δ p _ (summable_sumMod _) _ _ n
  · unfold cplBound
    exact mul_nonneg (Real.rpow_nonneg hJ.le _) (sq_nonneg _)
  · unfold cplBound
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hJ.le _) (sq_nonneg _)) (Real.rpow_nonneg (by linarith) _)
  · exact fun t ht => mom_sumMod P p μ hF hsum hmom t ht n .aTr
  · exact fun t ht => mom_sumMod P p μ hF hsum hmom t ht n .aTrDt

include hF haP hsum hmom in
/-- **One mode of `ℒ₀`.** -/
theorem prob_L0_mode (hL1 : 1 ≤ P.L) (n : Fin P.d → ℤ) :
    μ (F ∩ {ω | ∃ t ∈ Icc (p : ℝ) (p + 1),
        jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) * Real.exp (-(20 * P.N (p + 1) : ℝ)) <
          ‖Lop P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP ω)) 0 (fun _ _ => 0) t n‖}) ≤
      ENNReal.ofReal ((2 * cplBound P p n .L0 + 2 * cplBound P p n .L0Dt) /
        (jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
          Real.exp (-(20 * P.N (p + 1) : ℝ))) ^ 2) := by
  have hJ := jbr_pos'' (latticePoint P.L n)
  have hL : 0 < P.L := by linarith
  have hL0 : 0 ≤ P.L := hL.le
  refine prob_sup_le μ hF
    (f := fun ω t => Lop P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP ω)) 0 (fun _ _ => 0) t n)
    (g := fun ω t => L0Dt P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP ω)) t n) ?_ ?_ ?_ ?_ ?_ ?_
    (mul_pos (Real.rpow_pos_of_pos hJ _) (Real.exp_pos _)) ?_ ?_
  · have heq : Function.uncurry (fun ω t => Lop P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP ω)) 0
        (fun _ _ => 0) t n) = fun z : Ω × ℝ =>
          ∫ s in (p : ℝ)..z.2, L0Dt P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP z.1)) s n := by
      funext z
      exact L0_eq P.L P.γ P.δ hL p _ (summable_sumMod _) _ z.2 n
    rw [heq]
    exact stronglyMeasurable_intervalIntegral_param
      (F := fun w : (Ω × ℝ) × ℝ => L0Dt P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP w.1.1)) w.2 n)
      (stronglyMeasurable_L0Dt' P.L P.γ P.δ (stronglyMeasurable_sumMod_fst_fst P haP)
        (fun z => summable_sumMod _) measurable_snd p _ n) measurable_snd _
  · exact stronglyMeasurable_L0Dt' P.L P.γ P.δ (stronglyMeasurable_sumMod_fst P haP)
      (fun z => summable_sumMod _) measurable_snd p _ n
  · intro ω _ t _ t₀ _
    exact L0_sub P.L P.γ P.δ hL p _ (summable_sumMod _) _ t t₀ n
  · intro ω _
    exact intervalIntegrable_L0Dt P.L P.γ P.δ p _ (summable_sumMod _) _ _ n
  · unfold cplBound
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hJ.le _) (sq_nonneg _)) (Real.exp_pos _).le
  · unfold cplBound
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hJ.le _) (sq_nonneg _))
      (Real.rpow_nonneg hL0 _)) (Real.exp_pos _).le
  · exact fun t ht => mom_sumMod P p μ hF hsum hmom t ht n .L0
  · exact fun t ht => mom_sumMod P p μ hF hsum hmom t ht n .L0Dt

include hF haP hsum hmom in
/-- **Part 1**: the probability on `F` that clause (1) or (2) of `fixedpoint` fails. -/
theorem part1_prob (hL1 : 1 ≤ P.L) (hΛ : (P.d : ℝ) + 1 ≤ P.Lambda (p + 1)) :
    μ (F ∩ {ω | aP ω ∉ Good1 P p}) ≤ ENNReal.ofReal (part1Bound P p) := by
  have hL0 : 0 ≤ P.L := by linarith
  set Λ : ℝ := (P.Lambda (p + 1) : ℝ) with hΛdef
  set M : ℝ := P.L ^ (100 * P.d : ℝ)
  have hM : 0 ≤ M := Real.rpow_nonneg hL0 _
  set K1 : ℝ := 2 * P.L ^ 2 * (1 + M) / Real.exp (3 * (P.N (p + 1) : ℝ)) ^ 2
  set K2 : ℝ := 2 * (P.L ^ 2 * Real.exp (-(100 * P.N (p + 1) : ℝ))) * (1 + M) /
    Real.exp (-(20 * P.N (p + 1) : ℝ)) ^ 2
  have hK1 : 0 ≤ K1 := by positivity
  have hK2 : 0 ≤ K2 := by positivity
  set E1 : (Fin P.d → ℤ) → Set Ω := fun n => F ∩ {ω | ∃ t ∈ Icc (p : ℝ) (p + 1),
    jbr (latticePoint P.L n) ^ (-(3 / 2 * Λ)) * Real.exp (3 * (P.N (p + 1) : ℝ)) <
      ‖aTr P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP ω)) t n‖}
  set E2 : (Fin P.d → ℤ) → Set Ω := fun n => F ∩ {ω | ∃ t ∈ Icc (p : ℝ) (p + 1),
    jbr (latticePoint P.L n) ^ (-(3 / 2 * Λ)) * Real.exp (-(20 * P.N (p + 1) : ℝ)) <
      ‖Lop P.L P.γ P.δ p (P.N (p + 1)) (sumMod (aP ω)) 0 (fun _ _ => 0) t n‖}
  have hsub : F ∩ {ω | aP ω ∉ Good1 P p} ⊆ ⋃ n, (E1 n ∪ E2 n) := by
    rintro ω ⟨hω, hbad⟩
    have hs := sumMod_of_summable (hsum ω hω)
    simp only [Good1, mem_ofPred_eq, not_and_or, not_forall, not_le, exists_prop] at hbad
    rcases hbad with ⟨t, ht, n, hn⟩ | ⟨t, ht, n, hn⟩
    · exact mem_iUnion.2 ⟨n, Or.inl ⟨hω, t, ht, by rw [hs]; exact hn⟩⟩
    · exact mem_iUnion.2 ⟨n, Or.inr ⟨hω, t, ht, by rw [hs]; exact hn⟩⟩
  have hr1 : ∀ n, μ (E1 n) ≤ ENNReal.ofReal (K1 * wt P.L Λ n) := fun n => by
    refine (prob_aTr_mode P p μ hF haP hsum hmom hL1 n).trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    exact ratio_eq (jbr_pos'' _) (Real.exp_pos _) (by unfold cplBound; ring) (by unfold cplBound; ring)
  have hr2 : ∀ n, μ (E2 n) ≤ ENNReal.ofReal (K2 * wt P.L Λ n) := fun n => by
    refine (prob_L0_mode P p μ hF haP hsum hmom hL1 n).trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    exact ratio_eq (jbr_pos'' _) (Real.exp_pos _) (by unfold cplBound; ring) (by unfold cplBound; ring)
  have hΛ' : (P.d : ℝ) + 1 ≤ Λ := hΛ
  have hwsum := summable_wt P.L hL1 hΛ'
  have hw0 : ∀ n : Fin P.d → ℤ, 0 ≤ wt P.L Λ n := fun n => (wt_pos P.L Λ n).le
  calc μ (F ∩ {ω | aP ω ∉ Good1 P p}) ≤ μ (⋃ n, (E1 n ∪ E2 n)) := measure_mono hsub
    _ ≤ ∑' n, μ (E1 n ∪ E2 n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal ((K1 + K2) * wt P.L Λ n) := ENNReal.tsum_le_tsum fun n =>
        (measure_union_le _ _).trans (by
          rw [add_mul, ENNReal.ofReal_add (mul_nonneg hK1 (hw0 n)) (mul_nonneg hK2 (hw0 n))]
          exact add_le_add (hr1 n) (hr2 n))
    _ = ENNReal.ofReal (∑' n, (K1 + K2) * wt P.L Λ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (add_nonneg hK1 hK2) (hw0 n))
          (hwsum.mul_left _)).symm
    _ ≤ ENNReal.ofReal (part1Bound P p) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left]
        unfold part1Bound
        refine mul_le_mul_of_nonneg_left ?_ (add_nonneg hK1 hK2)
        exact hwsum.tsum_le_tsum (fun n => wt_le hΛ' n) (summable_jbr_rpow_neg hL1)

end Part1

end WaveTurbulence.Fixedpt
