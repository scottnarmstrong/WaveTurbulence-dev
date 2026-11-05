/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.FixedptDraft.X3Numerics
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Gates

/-!
# X3: assembly of B1.3 `fixedpoint` (T L780–L794, proof L2306–L2338)

`fixedpoint_of_parts : WTPrefix CplMomBody → WTPrefix Part2Body → Gates.FixedpointGate`.

The ingredients:
- `CplMomBody`: the couple moments of Part 1, from the gates and O-X3-CPL (`cplMoments_of_gates`).
- `Part2Body`: (fixedest3) in event form. The excluded data set is measurable and phase-stable, has
  probability `≤ e^{-4N}/2` on `Fev p`, and outside it `‖𝒴‖, ‖𝒲‖ ≤ 1/2` and `‖𝒳‖ ≤ e^{2N}` on `Z`.
  **This is the temporary obligation O-X3-PART2**, to be proved in `X3-Part2`.

The proof, for each sample and `L ≥ gFix(d, 𝔇)`:
1. Exclude the data outside `SumData ∩ Good1Q ∩ C₂`, by `exists_symmetric_subevent`. The non-rapid data
   are null. Part 1 costs `≤ e^{-4N}/2` (`part1_prob`, `part1Bound_le`) and Part 2 costs `≤ e^{-4N}/2`.
2. On the remaining event, clauses (1)–(2) are `Good1`. Clauses (3)–(6) are `fixedpoint_core` with
   `α = κ = e^{3N}`, `ε₀ = e^{-20N}`, `ρ = e^{-10N}` and `M = e^{2N}`, since `triK ≤ e^{4N}/18`.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.Fixedpt

open MeasureTheory Set SysAPI
open scoped ENNReal

universe u

/-- **The body of O-X3-PART2** (temporary): (fixedest3), T L2316–L2336, as a phase-stable measurable
condition on `a(p)`. -/
def Part2Body (P : WTParams) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
  ∀ p : ℕ, p < P.D →
  ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
    (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
  ∃ C : Set ((Fin P.d → ℤ) → ℂ), MeasurableSet C ∧
    (∀ φ, IsCubicPhase φ → ∀ b ∈ C, (Summable fun k => ‖b k‖) → (fun k => φ k * b k) ∈ C) ∧
    μ (Fev p ∩ {ω | a ω p ∉ C}) ≤ ENNReal.ofReal (Real.exp (-(4 * P.N (p + 1) : ℝ)) / 2) ∧
    ∀ b ∈ C, (Summable fun k => ‖b k‖) →
      ∀ c ∈ ZSpace (d := P.d) P.L (5 / 4 * P.Lambda (p + 1)) p,
        ZNorm P.L (5 / 4 * P.Lambda (p + 1)) (Yop P.L P.γ P.δ p (P.N (p + 1)) b c) ≤
            2⁻¹ * ZNorm P.L (5 / 4 * P.Lambda (p + 1)) c ∧
        ZNorm P.L (5 / 4 * P.Lambda (p + 1)) (Wop P.L P.γ P.δ p (P.N (p + 1)) b c) ≤
            2⁻¹ * ZNorm P.L (5 / 4 * P.Lambda (p + 1)) c ∧
        ZNorm P.L (5 / 4 * P.Lambda (p + 1)) (Xop P.L P.γ P.δ p (P.N (p + 1)) b c) ≤
            ENNReal.ofReal (Real.exp (2 * P.N (p + 1))) * ZNorm P.L (5 / 4 * P.Lambda (p + 1)) c

theorem CplMomBody_update (P : WTParams) (C₁ C₂ : ℝ) :
    CplMomBody.{u} {P with C₁ := C₁, C₂ := C₂} = CplMomBody.{u} P := by
  simp only [CplMomBody, AnsatzAt, truncSum, inputsF_update_x2, WTParams.theta, WTParams.Lambda,
    N_update_x2, R_update_x2, cplRand, cplBound]

/-- `L` large after `d` **and `𝔇`**; and `γ ∈ (0,1)`, `0 < δ ≤ 1`. -/
theorem WTPrefix.large {Q : WTParams → Prop} (h : WTPrefix Q) (g : ℕ → ℕ → ℝ) :
    WTPrefix fun P => Q P ∧ 3 ≤ P.d ∧ P.γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < P.δ ∧ P.δ ≤ 1 ∧ g P.d P.D ≤ P.L ∧
      2 ≤ P.L := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ ⟨hδ.1, hδ.2.trans (min_le_left _ _)⟩ D hD hτD
  refine ⟨C₂, hC₂, max L₀ (g d D), hL₀.trans (le_max_left _ _), fun L hL => ?_⟩
  exact ⟨H L ((le_max_left _ _).trans hL), hd, hγ, hδ.1, hδ.2.trans (min_le_right _ _),
    (le_max_right _ _).trans hL, hL₀.trans ((le_max_left _ _).trans hL)⟩

/-- The threshold for `L`. -/
noncomputable def gFix (d D : ℕ) : ℝ :=
  max (Real.exp (100 * d + 11)) (max (16 * 2 ^ (d + 1) * latConst d)
    (18 * 3 ^ (5 / 4 * ((40 * d) ^ D : ℕ) + 1 : ℝ) * 4 ^ (d + 1) * latConst d ^ 2))

/-! ## Scalar facts -/

theorem fix_small {N K : ℝ} (hN : 1 ≤ N) (hK0 : 0 ≤ K) (hK : K ≤ Real.exp (4 * N) / 18) :
    Real.exp (3 * N) * (Real.exp (-(20 * N)) + 3 * K * Real.exp (-(10 * N)) ^ 2 * Real.exp (3 * N) +
      K * Real.exp (-(10 * N)) ^ 3) ≤ Real.exp (-(10 * N)) := by
  have e1 : Real.exp (3 * N) * Real.exp (-(20 * N)) = Real.exp (-(10 * N)) * Real.exp (-(7 * N)) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (3 * N) * (3 * K * Real.exp (-(10 * N)) ^ 2 * Real.exp (3 * N)) =
      3 * K * Real.exp (-(4 * N)) * Real.exp (-(10 * N)) := by
    rw [← Real.exp_nat_mul]
    have : Real.exp (3 * N) * Real.exp ((2 : ℕ) * -(10 * N)) * Real.exp (3 * N) =
        Real.exp (-(4 * N)) * Real.exp (-(10 * N)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
    linear_combination 3 * K * this
  have e3 : Real.exp (3 * N) * (K * Real.exp (-(10 * N)) ^ 3) =
      K * Real.exp (-(4 * N)) * (Real.exp (-(13 * N)) * Real.exp (-(10 * N))) := by
    rw [← Real.exp_nat_mul]
    have : Real.exp (3 * N) * Real.exp ((3 : ℕ) * -(10 * N)) =
        Real.exp (-(4 * N)) * (Real.exp (-(13 * N)) * Real.exp (-(10 * N))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
    linear_combination K * this
  have hKe : K * Real.exp (-(4 * N)) ≤ 1 / 18 := by
    have h4 : Real.exp (4 * N) * Real.exp (-(4 * N)) = 1 := by rw [← Real.exp_add]; simp
    calc K * Real.exp (-(4 * N)) ≤ Real.exp (4 * N) / 18 * Real.exp (-(4 * N)) := by gcongr
      _ = 1 / 18 := by rw [div_mul_eq_mul_div, h4]
  have h7 : Real.exp (-(7 * N)) ≤ 1 / 2 := by
    have : Real.exp (-(7 * N)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    refine this.trans ?_
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h13 : Real.exp (-(13 * N)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE := Real.exp_pos (-(10 * N))
  have hKe0 : 0 ≤ K * Real.exp (-(4 * N)) := mul_nonneg hK0 (Real.exp_pos _).le
  rw [mul_add, mul_add, e1, e2, e3]
  nlinarith [mul_le_mul_of_nonneg_right h7 hE.le, mul_le_mul_of_nonneg_right hKe hE.le,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h13 hE.le) hKe0]

theorem fix_contr {N K : ℝ} (hN : 1 ≤ N) (hK0 : 0 ≤ K) (hK : K ≤ Real.exp (4 * N) / 18) :
    Real.exp (3 * N) * (6 * K * Real.exp (-(10 * N)) * Real.exp (3 * N) + 3 * K * Real.exp (-(10 * N)) ^ 2) ≤
      2⁻¹ := by
  have e1 : Real.exp (3 * N) * (6 * K * Real.exp (-(10 * N)) * Real.exp (3 * N)) = 6 * K * Real.exp (-(4 * N)) := by
    have : Real.exp (3 * N) * Real.exp (-(10 * N)) * Real.exp (3 * N) = Real.exp (-(4 * N)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    linear_combination 6 * K * this
  have e2 : Real.exp (3 * N) * (3 * K * Real.exp (-(10 * N)) ^ 2) =
      3 * K * Real.exp (-(4 * N)) * Real.exp (-(13 * N)) := by
    rw [← Real.exp_nat_mul]
    have : Real.exp (3 * N) * Real.exp ((2 : ℕ) * -(10 * N)) = Real.exp (-(4 * N)) * Real.exp (-(13 * N)) := by
      rw [← Real.exp_add, ← Real.exp_add]; push_cast; ring_nf
    linear_combination 3 * K * this
  have hKe : K * Real.exp (-(4 * N)) ≤ 1 / 18 := by
    have h4 : Real.exp (4 * N) * Real.exp (-(4 * N)) = 1 := by rw [← Real.exp_add]; simp
    calc K * Real.exp (-(4 * N)) ≤ Real.exp (4 * N) / 18 * Real.exp (-(4 * N)) := by gcongr
      _ = 1 / 18 := by rw [div_mul_eq_mul_div, h4]
  have h13 : Real.exp (-(13 * N)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hKe0 : 0 ≤ K * Real.exp (-(4 * N)) := mul_nonneg hK0 (Real.exp_pos _).le
  rw [mul_add, e1, e2]
  nlinarith [mul_le_mul_of_nonneg_left h13 hKe0]

theorem Lambda_ge (P : WTParams) {p : ℕ} (hp : p < P.D) (hd : 1 ≤ P.d) :
    40 * P.d ≤ P.Lambda (p + 1) ∧ P.Lambda (p + 1) ≤ (40 * P.d) ^ P.D := by
  unfold WTParams.Lambda
  have h1 : 1 ≤ 40 * P.d := by omega
  refine ⟨?_, Nat.pow_le_pow_right h1 (by omega)⟩
  exact Nat.le_self_pow (by omega) _

/-! ## The assembly -/

/-- **B1.3 `fixedpoint`, from the Part 1 couple moments and O-X3-PART2.** -/
theorem fixedpoint_of_parts (hcpl : WTPrefix CplMomBody.{u}) (h2 : WTPrefix Part2Body.{u}) :
    Gates.FixedpointGate.{u} := by
  have h := Fixedpt.WTPrefix.large (WTPrefix.and (fun P C₁ C₂ h => by rw [CplMomBody_update]; exact h) hcpl h2)
    gFix
  refine h.mono ?_
  rintro P ⟨⟨hC, h2P⟩, hd, hγ, hδ0, hδ1, hLg, hL2⟩
  intro Ω _ μ _ g hg p hp a Fev R E Et hA
  have hL1 : 1 ≤ P.L := by linarith
  have hL0 : 0 < P.L := by linarith
  have hd1 : 1 ≤ P.d := by omega
  have hLe : Real.exp (100 * P.d + 11) ≤ P.L := le_trans (le_max_left _ _) hLg
  have hLa : 16 * 2 ^ (P.d + 1) * latConst P.d ≤ P.L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLg
  have hLb : 18 * 3 ^ (5 / 4 * ((40 * P.d) ^ P.D : ℕ) + 1 : ℝ) * 4 ^ (P.d + 1) * latConst P.d ^ 2 ≤ P.L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLg
  set N : ℕ := P.N (p + 1) with hNdef
  have hNlog := WTParams.N_ge_log P hd1 hLe (p + 1)
  have hlogL : 0 ≤ Real.log P.L := Real.log_nonneg hL1
  have hN1 : (1 : ℝ) ≤ N := by
    have : (0 : ℝ) ≤ 100 * P.d * Real.log P.L := by positivity
    linarith
  obtain ⟨hΛ40, hΛD⟩ := Lambda_ge P hp hd1
  set Λ' : ℕ := P.Lambda (p + 1) with hΛ'def
  have hΛ'r : (P.d : ℝ) + 1 ≤ Λ' := by
    have : ((40 * P.d : ℕ) : ℝ) ≤ Λ' := by exact_mod_cast hΛ40
    push_cast at this
    have : (1 : ℝ) ≤ P.d := by exact_mod_cast hd1
    linarith
  set Λ : ℝ := 5 / 4 * (Λ' : ℝ) with hΛdef
  have hΛ : (P.d : ℝ) + 1 ≤ Λ := by
    have : (0 : ℝ) ≤ Λ' := Nat.cast_nonneg _
    linarith
  -- the ansatz at `p`
  have hAp : AnsatzAt P μ g a Fev R E Et p := hA p le_rfl
  have hpI : (p : ℝ) ∈ Icc (0 : ℝ) p := ⟨Nat.cast_nonneg p, le_rfl⟩
  have hsol : ∀ ω ∈ Fev p, IsASolution P.L P.γ P.δ p (initialCoeff P.L P.φin g ω) (a ω) :=
    fun ω hω => SysAPI.AnsatzAt.isASolution hAp hω
  have haP : ∀ k, Measurable fun ω => a ω p k := fun k => SysAPI.AnsatzAt.measurable hAp hpI k
  have hsum : ∀ ω ∈ Fev p, Summable fun k => ‖a ω p k‖ :=
    fun ω hω => SysAPI.IsASolution.summable_norm hL0 (hsol ω hω) hpI
  have hmom := hC Ω μ g hg p hp a Fev R E Et hA
  obtain ⟨C2, hC2m, hC2inv, hC2prob, hC2op⟩ := h2P Ω μ g hg p hp a Fev R E Et hA
  -- the excluded event
  set C : Set ((Fin P.d → ℤ) → ℂ) := {b | Summable fun k => ‖b k‖} ∩ Good1Q P p ∩ C2 with hCdef
  have hCm : MeasurableSet C :=
    (measurableSet_summable_norm.inter (measurableSet_good1Q P p hL0)).inter hC2m
  have hCinv : ∀ φ, IsCubicPhase φ → ∀ b ∈ C, (fun k => φ k * b k) ∈ C := by
    rintro φ hφ b ⟨⟨hbs, hb1⟩, hb2⟩
    exact ⟨⟨(summable_mul_phase hφ).2 hbs, good1Q_mul_phase P p hL0 hφ hbs hb1⟩, hC2inv φ hφ b hb2 hbs⟩
  obtain ⟨F', hF'sub, hF'm, hF'sym, hF'C, hdiff⟩ := exists_symmetric_subevent hL0 P.φin hg.1
    (Nat.cast_nonneg p) (SysAPI.AnsatzAt.isSymmetricEvent hAp) hsol hCm hCinv
  refine ⟨F', hF'sub, hF'm, hF'sym, ?_, ?_⟩
  · -- the probability
    have hrapid : μ (initialRapidEvent P.L P.φin g)ᶜ = 0 :=
      ae_iff.1 (initialRapidEvent_ae hL0 P.φin g fun n => ⟨(hg.1 n).aemeasurable, hg.2.2 n⟩)
    have hsub2 : Fev p ∩ {ω | a ω p ∉ C} ⊆
        (Fev p ∩ {ω | a ω p ∉ Good1 P p}) ∪ (Fev p ∩ {ω | a ω p ∉ C2}) := by
      rintro ω ⟨hω, hnot⟩
      by_cases h1 : a ω p ∈ Good1 P p
      · exact Or.inr ⟨hω, fun h2 => hnot ⟨⟨hsum ω hω, good1Q_of_good1 P p (hsum ω hω) h1⟩, h2⟩⟩
      · exact Or.inl ⟨hω, h1⟩
    have hP1 : μ (Fev p ∩ {ω | a ω p ∉ Good1 P p}) ≤
        ENNReal.ofReal (Real.exp (-(4 * (N : ℝ))) / 2) :=
      (part1_prob P p μ (SysAPI.AnsatzAt.measurableSet hAp) haP hsum hmom hL1 hΛ'r).trans
        (ENNReal.ofReal_le_ofReal (part1Bound_le P p hd1 hLe hLa))
    have hE : 0 ≤ Real.exp (-(4 * (N : ℝ))) / 2 := by positivity
    have htot : μ (Fev p \ F') ≤ ENNReal.ofReal (Real.exp (-(4 * (N : ℝ)))) :=
      calc μ (Fev p \ F') ≤ μ ((initialRapidEvent P.L P.φin g)ᶜ ∪ (Fev p ∩ {ω | a ω p ∉ C})) :=
            measure_mono hdiff
        _ ≤ μ (initialRapidEvent P.L P.φin g)ᶜ + μ (Fev p ∩ {ω | a ω p ∉ C}) := measure_union_le _ _
        _ ≤ 0 + (μ (Fev p ∩ {ω | a ω p ∉ Good1 P p}) + μ (Fev p ∩ {ω | a ω p ∉ C2})) :=
            add_le_add (le_of_eq hrapid) ((measure_mono hsub2).trans (measure_union_le _ _))
        _ ≤ 0 + (ENNReal.ofReal (Real.exp (-(4 * (N : ℝ))) / 2) +
              ENNReal.ofReal (Real.exp (-(4 * (N : ℝ))) / 2)) := by
            gcongr
        _ = ENNReal.ofReal (Real.exp (-(4 * (N : ℝ)))) := by
            rw [zero_add, ← ENNReal.ofReal_add hE hE]
            congr 1
            ring
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le htot
  · -- the clauses
    intro ω hω
    dsimp only
    obtain ⟨⟨hbs, hb1⟩, hb2⟩ := hF'C ω hω
    have hG1 := good1_of_good1Q P p hL0 hbs hb1
    have hwt : ∀ n : Fin P.d → ℤ, jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) ≤
        wt P.L Λ n := fun n =>
      Real.rpow_le_rpow_of_exponent_le (one_le_jbr _) (by
        have : (0 : ℝ) ≤ Λ' := Nat.cast_nonneg _
        rw [hΛdef]; linarith)
    have hα : ∀ s ∈ Icc (p : ℝ) (p + 1), ∀ k, ‖aTr P.L P.γ P.δ p N (a ω p) s k‖ ≤
        Real.exp (3 * (N : ℝ)) * wt P.L Λ k := fun s hs k => by
      refine (hG1.1 s hs k).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hwt k) (Real.exp_pos _).le
    have hL0eq : ∀ (b : Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) (t : ℝ) (n : Fin P.d → ℤ),
        Lop P.L P.γ P.δ p N (a ω p) 0 b t n = Lop P.L P.γ P.δ p N (a ω p) 0 (fun _ _ => 0) t n :=
      fun b t n => by
        rw [L0_eq P.L P.γ P.δ hL0 p N hbs b t n, L0_eq P.L P.γ P.δ hL0 p N hbs (fun _ _ => 0) t n]
    have h0 : ∀ (b : ArrI p P.d) (t : Icc (p : ℝ) (p + 1)) (n : Fin P.d → ℤ),
        ‖Lop P.L P.γ P.δ p N (a ω p) 0 b t n‖ ≤ Real.exp (-(20 * (N : ℝ))) * wt P.L Λ n := fun b t n => by
      rw [hL0eq]
      refine (hG1.2 t t.2 n).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hwt n) (Real.exp_pos _).le
    have hops := hC2op (a ω p) hb2 hbs
    have hK0 : 0 ≤ triK P.d P.L P.γ P.δ Λ := triK_nonneg P.L P.γ P.δ
    have hKle : triK P.d P.L P.γ P.δ Λ ≤ Real.exp (4 * (N : ℝ)) / 18 := by
      refine triK_le P p hd1 hLe hγ.2 hδ0 hδ1 (le_trans ?_ hLb)
      have h3 : (3 : ℝ) ^ (Λ + 1) ≤ 3 ^ (5 / 4 * ((40 * P.d) ^ P.D : ℕ) + 1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have : (Λ' : ℝ) ≤ ((40 * P.d) ^ P.D : ℕ) := by exact_mod_cast hΛD
        rw [hΛdef]; linarith
      have hS := latConst_nonneg P.d
      gcongr
    have hM : 2 * ENNReal.ofReal (Real.exp (2 * (N : ℝ))) ≤ ENNReal.ofReal (Real.exp (3 * (N : ℝ))) := by
      rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      have he : (2 : ℝ) ≤ Real.exp (N : ℝ) := by
        have := Real.add_one_le_exp (N : ℝ)
        linarith
      calc 2 * Real.exp (2 * (N : ℝ)) ≤ Real.exp (N : ℝ) * Real.exp (2 * (N : ℝ)) := by
            gcongr
        _ = Real.exp (3 * (N : ℝ)) := by rw [← Real.exp_add]; ring_nf
    obtain ⟨c3, c4, c5, c6, c7⟩ := fixedpoint_core P.L P.γ P.δ N hbs hL1 hΛ (α := Real.exp (3 * (N : ℝ)))
      (ε₀ := Real.exp (-(20 * (N : ℝ)))) (ρ := Real.exp (-(10 * (N : ℝ)))) (κ := Real.exp (3 * (N : ℝ)))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le hα h0
      (ENNReal.ofReal (Real.exp (2 * (N : ℝ)))) hM
      (fun c hc => (hops c hc).2.2) (fun c hc => (hops c hc).1) (fun c hc => (hops c hc).2.1)
      (by
        have := fix_small hN1 hK0 hKle
        have e : Real.exp (-(20 * (N : ℝ))) = Real.exp (-(10 * (N : ℝ))) ^ 2 := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        calc Real.exp (3 * (N : ℝ)) * (Real.exp (-(20 * (N : ℝ))) +
              3 * triK P.d P.L P.γ P.δ Λ * Real.exp (-(10 * (N : ℝ))) ^ 2 * Real.exp (3 * (N : ℝ)) +
              triK P.d P.L P.γ P.δ Λ * Real.exp (-(10 * (N : ℝ))) ^ 3) ≤ Real.exp (-(10 * (N : ℝ))) := this
          _ = _ := rfl)
      (fix_contr hN1 hK0 hKle)
    exact ⟨fun t ht n => hG1.1 t ht n, fun b t n => by rw [hL0eq]; exact hG1.2 t t.2 n,
      c3, c4, c5, c6, c7⟩

/-- **B1.3 `fixedpoint` from the gates B1.12, B1.2, B1.5, O-X3-CPL and O-X3-PART2.** -/
theorem fixedpoint_of_gates_part2 (hG : LayergardenFlowerGate) (hL : Gates.LayergardenGate)
    (hW : Gates.WkeTaylorGate) (hC : OX3Cpl.{u}) (h2 : WTPrefix Part2Body.{u}) : Gates.FixedpointGate.{u} :=
  fixedpoint_of_parts (cplMoments_of_gates hG hL hW hC) h2

end WaveTurbulence.Fixedpt
